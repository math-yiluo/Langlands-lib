import Langlands.Global.AdelicNormOneDecomposition
import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.GroupScheme.Rational.CharacterRestrictionInjective
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndexProof
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.Automorphic.GroupSchemeAmbient

/-! # A continuous left-equivariant retraction onto the norm-one adelic group

For a connected reductive group `G` over a number field, `G(𝔸_F)¹` is the common kernel of the
absolute values of the rational characters. Removing from `x` on the right the point of a split
component `A_G` with the same character absolute values gives a continuous map
`G(𝔸_F) → G(𝔸_F)¹` that is the identity on `G(𝔸_F)¹` and commutes with left multiplication by
`G(𝔸_F)¹`. Composing a continuous left `G(F)`-invariant function on `G(𝔸_F)¹` with it gives a
continuous left `G(F)`-invariant extension to `G(𝔸_F)`. -/

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
variable (i : T.toGrp ⟶ G)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (I : Type u) [Fintype I]
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

/-- Remove on the right the positive point with the same character logarithm. -/
def normOneRightFactor (x : AdelicGroupPoints F G) : normOneSubgroup F G :=
  ⟨x * (positivePointMap F G T i (positiveFactor F G T i hi I e x))⁻¹, by
    apply (characterLog_eq_zero_iff F G _).mp
    change characterLogHom F G
      (x * (positivePointMap F G T i (positiveFactor F G T i hi I e x))⁻¹) = 1
    rw [map_mul, map_inv, characterLogHom_positivePointMap F G T i hi I e,
      positiveFactor_apply, ContinuousMulEquiv.apply_symm_apply, mul_inv_cancel]⟩

@[simp] theorem normOneRightFactor_val (x : AdelicGroupPoints F G) :
    (normOneRightFactor F G T i hi I e x : AdelicGroupPoints F G) =
      x * (positivePointMap F G T i (positiveFactor F G T i hi I e x))⁻¹ := rfl

theorem continuous_normOneRightFactor [IsAffine G.X.left] : Continuous (normOneRightFactor F G T i hi I e) :=
  Continuous.subtype_mk (continuous_id.mul
    ((positivePointMap F G T i).continuous.comp (positiveFactor F G T i hi I e).continuous).inv) _

@[simp] theorem normOneRightFactor_normOne (n : normOneSubgroup F G) :
    normOneRightFactor F G T i hi I e (n : AdelicGroupPoints F G) = n := by
  apply Subtype.ext
  rw [normOneRightFactor_val, positiveFactor_normOne, map_one, inv_one, mul_one]

theorem normOneRightFactor_mul_left (g : normOneSubgroup F G) (x : AdelicGroupPoints F G) :
    normOneRightFactor F G T i hi I e ((g : AdelicGroupPoints F G) * x) =
      g * normOneRightFactor F G T i hi I e x := by
  apply Subtype.ext
  rw [normOneRightFactor_val, Subgroup.coe_mul, normOneRightFactor_val, map_mul,
    positiveFactor_normOne, one_mul, mul_assoc]

theorem normOneRightFactor_mul_right (hc : IsCentral i) (x : AdelicGroupPoints F G)
    (g : normOneSubgroup F G) :
    normOneRightFactor F G T i hi I e (x * (g : AdelicGroupPoints F G)) =
      normOneRightFactor F G T i hi I e x * g := by
  apply Subtype.ext
  rw [normOneRightFactor_val, Subgroup.coe_mul, normOneRightFactor_val, map_mul,
    positiveFactor_normOne, mul_one]
  have hcomm := (positivePointMap_commute F G T i hc (positiveFactor F G T i hi I e x)
    (g : AdelicGroupPoints F G)).inv_left
  rw [mul_assoc, ← hcomm.eq, ← mul_assoc]

end Langlands.Global.PositiveRealTorus

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints PositiveRealTorus

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- **Norm-one retraction.** A connected reductive group over a number field admits a continuous
map `r : G(𝔸_F) → G(𝔸_F)¹` that is the identity on `G(𝔸_F)¹` and satisfies `r(g x) = g r(x)` and
`r(x g) = r(x) g` for `g ∈ G(𝔸_F)¹`. -/
theorem exists_normOneRetraction (hG : IsConnectedReductive G) :
    ∃ r : AdelicGroupPoints F G → normOneSubgroup F G, Continuous r ∧
      (∀ n : normOneSubgroup F G, r n = n) ∧
      (∀ (g : normOneSubgroup F G) (x : AdelicGroupPoints F G),
        r ((g : AdelicGroupPoints F G) * x) = g * r x) ∧
      ∀ (x : AdelicGroupPoints F G) (g : normOneSubgroup F G),
        r (x * (g : AdelicGroupPoints F G)) = r x * g := by
  obtain ⟨T, i, hs⟩ := exists_isSplitComponent G
  have hi : Function.Injective (characterRestrict i) :=
    characterRestrict_injective_of_centralSplitTorusCharacter centralSplitTorusCharacter hG hs
  have : (characterRestrict i).range.FiniteIndex :=
    characterRestrictionFiniteIndexStatement F G hG T i hs
  obtain ⟨I, hI, ⟨e⟩⟩ := hs.1.1.1
  let : Fintype I := Fintype.ofFinite I
  exact ⟨normOneRightFactor F G T i hi I e, continuous_normOneRightFactor F G T i hi I e,
    normOneRightFactor_normOne F G T i hi I e, normOneRightFactor_mul_left F G T i hi I e,
    normOneRightFactor_mul_right F G T i hi I e hs.1.2⟩

end Langlands.Global
