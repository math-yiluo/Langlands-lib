import Langlands.Representation.Plancherel.RationalNormKernelRemarksStatements
import Langlands.GroupScheme.Rational.SplitTorusCharacterRestriction
import Langlands.Representation.Plancherel.RationalUnramifiedRestriction

/-! # Proof of Renard V.2.5: `⁰A₁ = A₁ ∩ ⁰A₂` for split tori `A₁ ⊆ A₂` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

/-- Renard V.2.5, last paragraph: `⁰A₁ = A₁ ∩ ⁰A₂` for split tori `A₁ ⊆ A₂`. -/
theorem rationalNormKernelRestriction : RationalNormKernelRestrictionStatement.{u} := by
  intro F _ _ _ _ A₁ A₂ f hA₂ hf
  apply le_antisymm
  · intro t ht
    have : IsClosedImmersion f.hom.hom.left := hf.2
    apply (mem_rationalCommonNormKernel A₁.toGrp t).mpr
    intro χ
    obtain ⟨χ', hχ'⟩ := hf.1.characterRestrict_surjective_of_mono hA₂ f χ
    have h := (mem_rationalCommonNormKernel A₂.toGrp _).mp ht χ'
    rw [← hχ', GroupScheme.rationalCharacterEval_characterRestrict]
    exact h
  · exact rationalCommonNormKernel_le_comap f

end Langlands.Plancherel
