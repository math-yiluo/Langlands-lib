import Langlands.GroupScheme.Rational.RelativeRank
import Langlands.GroupScheme.Rational.CharactersStatement
import Langlands.LinearAlgebra.RationalFiniteIndex

/-! # Rational scalar extension of integral character restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Integral injectivity and finite-index image make the actual rationalized
character restriction bijective. -/
theorem rationalCharacterRestrictRat_bijective_of_integralRestriction (f : H ⟶ G)
    (hinj : Function.Injective (characterRestrict f))
    (hindex : (characterRestrict f).range.FiniteIndex) :
    Function.Bijective (rationalCharacterRestrictRat f) :=
  rationalization_bijective (characterRestrict f) hinj hindex

variable {A : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The actual character restriction to a commutative group scheme, viewed as a
rational linear equivalence once the integral restriction facts are known. -/
def rationalCharacterRestrictRatEquiv (a : A.toGrp ⟶ G)
    (hinj : Function.Injective (characterRestrict a))
    (hindex : (characterRestrict a).range.FiniteIndex) :
    (ℚ ⊗[ℤ] rationalCharacters G) ≃ₗ[ℚ] (ℚ ⊗[ℤ] characterLattice A) :=
  rationalizationEquiv (characterRestrict a) hinj hindex

@[simp]
theorem rationalCharacterRestrictRatEquiv_apply (a : A.toGrp ⟶ G)
    (hinj : Function.Injective (characterRestrict a))
    (hindex : (characterRestrict a).range.FiniteIndex)
    (v : ℚ ⊗[ℤ] rationalCharacters G) :
    rationalCharacterRestrictRatEquiv a hinj hindex v =
      rationalCharacterRestrictRat a v := rfl

/-- The finite-index integral restriction identities imply the corresponding
rational rank identity. This equality alone makes no finiteness assertion. -/
theorem rationalCharacterRank_eq_splitTorusRank_of_integralRestriction
    (a : A.toGrp ⟶ G) (hinj : Function.Injective (characterRestrict a))
    (hindex : (characterRestrict a).range.FiniteIndex) :
    rationalCharacterRank G = splitTorusRank A :=
  (rationalCharacterRestrictRatEquiv a hinj hindex).finrank_eq

/-- Consume the existing integral character-restriction statement to obtain
rational bijectivity for any actual split component. -/
theorem rationalCharacterRestrictRat_bijective_of_characterRestriction
    (hrestriction : CharacterRestrictionStatement.{u})
    (hG : IsConnectedReductive G) {a : A.toGrp ⟶ G} (ha : IsSplitComponent a) :
    Function.Bijective (rationalCharacterRestrictRat a) := by
  obtain ⟨hinj, hindex⟩ := hrestriction k G hG A a ha
  exact rationalCharacterRestrictRat_bijective_of_integralRestriction a hinj hindex

/-- Consume integral restriction to identify the rational-character rank with
the full character rank of any actual split component. -/
theorem rationalCharacterRank_eq_splitTorusRank_of_characterRestriction
    (hrestriction : CharacterRestrictionStatement.{u})
    (hG : IsConnectedReductive G) {a : A.toGrp ⟶ G} (ha : IsSplitComponent a) :
    rationalCharacterRank G = splitTorusRank A := by
  obtain ⟨hinj, hindex⟩ := hrestriction k G hG A a ha
  exact rationalCharacterRank_eq_splitTorusRank_of_integralRestriction a hinj hindex

/-- The two rational consequences needed by the intrinsic rank and complement
proofs, derived from the integral character-restriction statement. -/
theorem rationalCharacterRestrictRat_consequences_of_characterRestriction
    (hrestriction : CharacterRestrictionStatement.{u})
    (hG : IsConnectedReductive G) {a : A.toGrp ⟶ G} (ha : IsSplitComponent a) :
    Function.Bijective (rationalCharacterRestrictRat a) ∧
      rationalCharacterRank G = splitTorusRank A :=
  ⟨rationalCharacterRestrictRat_bijective_of_characterRestriction hrestriction hG ha,
    rationalCharacterRank_eq_splitTorusRank_of_characterRestriction hrestriction hG ha⟩

end Langlands.GroupScheme
