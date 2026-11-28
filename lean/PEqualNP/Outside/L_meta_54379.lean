import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54379

def circuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [5, 6]⟩,
    ⟨.or, [4, 8]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.and, [1, 12]⟩,
    ⟨.or, [10, 7]⟩,
    ⟨.and, [2, 14]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [0, 13]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [17, 18]⟩], 19⟩

end PEqualNP.Outside.L_meta_54379

theorem PEqualNP.Outside.L_meta_54379 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (321023 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  refine ⟨PEqualNP.Outside.L_meta_54379.circuit, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_54379.circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
