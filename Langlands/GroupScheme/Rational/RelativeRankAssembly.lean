import Langlands.GroupScheme.Rational.RelativeRankStatement
import Langlands.GroupScheme.Rational.RelativeCentralDirectionsStatement
import Langlands.GroupScheme.Rational.SplitTorusRationalRank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection

/-! # Rank assembly from independent geometric comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

section Complement

variable [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G)

/-- Sum of a root direction and the restriction of a rational character, as an
actual linear equivalence when the independent complement and injectivity hold. -/
def relativeRootCharacterEquiv
    (hcompl : IsCompl (relativeRootSpan i) (rationalCharacterRestrictRat i).range)
    (hinj : Function.Injective (rationalCharacterRestrictRat i)) :
    (relativeRootSpan i × (ℚ ⊗[ℤ] rationalCharacters G)) ≃ₗ[ℚ]
      (ℚ ⊗[ℤ] characterLattice T) :=
  ((LinearEquiv.refl ℚ (relativeRootSpan i)).prodCongr
    (LinearEquiv.ofInjective (rationalCharacterRestrictRat i) hinj)).trans
      (Submodule.prodEquivOfIsCompl _ _ hcompl)

@[simp] theorem relativeRootCharacterEquiv_apply
    (hcompl : IsCompl (relativeRootSpan i) (rationalCharacterRestrictRat i).range)
    (hinj : Function.Injective (rationalCharacterRestrictRat i))
    (x : relativeRootSpan i) (χ : ℚ ⊗[ℤ] rationalCharacters G) :
    relativeRootCharacterEquiv i hcompl hinj (x, χ) =
      (x : ℚ ⊗[ℤ] characterLattice T) + rationalCharacterRestrictRat i χ := rfl

/-- Finite-dimensional additivity of full rank from the independent rational
root/character complement and restriction injectivity. -/
theorem splitTorusRank_eq_relativeRootRank_add_rationalCharacterRank
    (hT : IsSplitTorus T.toGrp)
    (hcompl : IsCompl (relativeRootSpan i) (rationalCharacterRestrictRat i).range)
    (hinj : Function.Injective (rationalCharacterRestrictRat i)) :
    splitTorusRank T = relativeRootRank i + rationalCharacterRank G := by
  have := hT.finite_characterLatticeRat
  have hrange : Module.finrank ℚ (rationalCharacterRestrictRat i).range =
      rationalCharacterRank G := LinearMap.finrank_range_of_inj hinj
  calc
    splitTorusRank T = relativeRootRank i +
        Module.finrank ℚ (rationalCharacterRestrictRat i).range :=
      (Submodule.finrank_add_eq_of_isCompl hcompl).symm
    _ = relativeRootRank i + rationalCharacterRank G := congrArg _ hrange

end Complement

/-- Transport of the published conjugacy statement's rank clause to the intrinsic
rational-character rank. This does not prove the conjugacy statement. -/
theorem splitRank_eq_splitTorusRank_of_conjugacyStatement
    (hConjugacy : MaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) :
    splitRank G = (splitTorusRank T : ℕ∞) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hi.isSplitSubtorus.1
  have := hI
  rw [splitTorusRank_eq_card_of_splitting e]
  exact ((hConjugacy k G hG).2 T i hi I e).symm

end Langlands.GroupScheme
