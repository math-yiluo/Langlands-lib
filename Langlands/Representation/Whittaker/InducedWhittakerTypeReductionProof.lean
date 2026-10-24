import Langlands.Representation.Whittaker.InducedWhittakerTypeReductionStatement
import Langlands.Representation.Whittaker.LocalizationDual
import Langlands.LinearAlgebra.DualTensorOneDimensionalProof

/-! # Algebraic reduction from localized heredity to Whittaker type -/

namespace Langlands

universe uF uV

private theorem submodule_nonzero_span_iff_finrank_one
    {k W : Type*} [Field k] [AddCommGroup W] [Module k W] (S : Submodule k W) :
    (∃ w : W, w ≠ 0 ∧ w ∈ S ∧ ∀ w', w' ∈ S → ∃ c : k, w' = c • w) ↔
      Module.finrank k S = 1 := by
  rw [← LinearAlgebra.nonzero_span_iff_finrank_one]
  constructor
  · rintro ⟨w, hw, hmem, hspan⟩
    refine ⟨⟨w, hmem⟩, ?_, ?_⟩
    · intro hz
      exact hw (congrArg Subtype.val hz)
    · intro w'
      obtain ⟨c, hc⟩ := hspan w'.val w'.property
      exact ⟨c, Subtype.ext hc⟩
  · rintro ⟨w, hw, hspan⟩
    refine ⟨w.val, ?_, w.property, ?_⟩
    · intro hz
      exact hw (Subtype.ext hz)
    · intro w' hmem
      obtain ⟨c, hc⟩ := hspan ⟨w', hmem⟩
      exact ⟨c, congrArg Subtype.val hc⟩

/-- The quotient-heredity comparison implies the original full functional-space iff. -/
theorem inducedWhittakerTypeReduction :
    InducedWhittakerTypeReductionStatement.{uF, uV} := by
  intro heredity p hp F
  let := F.canonicalTopologicalData.topology
  intro n B
  let := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
  intro V _ _ π ψ hc hne hu hadm hfinite
  obtain ⟨e⟩ := heredity p hp F n B V π ψ hc hne hu hadm hfinite
  dsimp only
  simp only [← Whittaker.mem_functionals_entrywiseCharacter_iff,
    submodule_nonzero_span_iff_finrank_one]
  rw [(Whittaker.functionalsLocalizationDualEquiv _ _ _).finrank_eq,
    LinearAlgebra.dual_finrank_one_iff, e.finrank_eq,
    LinearAlgebra.piTensor_finrank_one_iff]
  apply forall_congr'
  intro i
  rw [(Whittaker.functionalsLocalizationDualEquiv _ _ _).finrank_eq,
    LinearAlgebra.dual_finrank_one_iff]

end Langlands
