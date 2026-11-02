import Langlands.Global.CharacterRestrictionRealDual
import Langlands.Global.PositiveRealTorusLog

/-! # An actual adelic logarithm section from finite-index character restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
variable (i : T.toGrp ⟶ G)

/-- The actual positive-torus point map into the ambient adelic group. -/
def positivePointMap : intrinsicSubgroup F T →ₜ* AdelicGroupPoints F G where
  toMonoidHom := (AdelicGroupPoints.map F T.toGrp G i).toMonoidHom.comp
    (intrinsicSubgroup F T).subtype
  continuous_toFun := (AdelicGroupPoints.map F T.toGrp G i).continuous.comp
    continuous_subtype_val

@[simp] theorem positivePointMap_apply (a : intrinsicSubgroup F T) :
    positivePointMap F G T i a = AdelicGroupPoints.map F T.toGrp G i a.val := rfl

variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]

/-- The genuine continuous real-dual equivalence, with addition written multiplicatively. -/
def restrictionLogEquiv :
    Multiplicative (RealCharacterDual F T.toGrp) ≃ₜ*
      Multiplicative (RealCharacterDual F G) where
  toFun ℓ := Multiplicative.ofAdd (realCharacterDualRestrictionEquiv F G T.toGrp i hi ℓ.toAdd)
  invFun ℓ := Multiplicative.ofAdd
    ((realCharacterDualRestrictionEquiv F G T.toGrp i hi).symm ℓ.toAdd)
  left_inv ℓ := (realCharacterDualRestrictionEquiv F G T.toGrp i hi).left_inv ℓ.toAdd
  right_inv ℓ := (realCharacterDualRestrictionEquiv F G T.toGrp i hi).right_inv ℓ.toAdd
  map_mul' ℓ m := (realCharacterDualRestrictionEquiv F G T.toGrp i hi).map_add ℓ.toAdd m.toAdd
  continuous_toFun := (realCharacterDualRestrictionEquiv F G T.toGrp i hi).continuous
  continuous_invFun := (realCharacterDualRestrictionEquiv F G T.toGrp i hi).symm.continuous

variable (I : Type u) [Fintype I]
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

/-- The ambient normalized logarithm identifies the actual intrinsic positive subgroup
with the entire ambient real character dual. -/
def positiveAmbientLogEquiv :
    intrinsicSubgroup F T ≃ₜ* Multiplicative (RealCharacterDual F G) :=
  (positiveLogEquiv F T I e).trans (restrictionLogEquiv F G T i hi)

/-- The forward map is exactly the ambient logarithm of the actual point image. -/
theorem characterLogHom_positivePointMap (a : intrinsicSubgroup F T) :
    characterLogHom F G (positivePointMap F G T i a) =
      positiveAmbientLogEquiv F G T i hi I e a :=
  characterLog_map F T.toGrp G i a.val

/-- Finite-index restriction constructs an actual continuous section of the ambient log. -/
def logSection : Multiplicative (RealCharacterDual F G) →ₜ* AdelicGroupPoints F G where
  toMonoidHom := (positivePointMap F G T i).toMonoidHom.comp
    (positiveAmbientLogEquiv F G T i hi I e).symm.toMulEquiv.toMonoidHom
  continuous_toFun := (positivePointMap F G T i).continuous.comp
    (positiveAmbientLogEquiv F G T i hi I e).symm.continuous

@[simp] theorem logSection_apply (ℓ : Multiplicative (RealCharacterDual F G)) :
    logSection F G T i hi I e ℓ = positivePointMap F G T i
      ((positiveAmbientLogEquiv F G T i hi I e).symm ℓ) := rfl

/-- The section is a right inverse on every actual real character functional. -/
@[simp] theorem characterLogHom_logSection (ℓ : Multiplicative (RealCharacterDual F G)) :
    characterLogHom F G (logSection F G T i hi I e ℓ) = ℓ := by
  rw [logSection_apply, characterLogHom_positivePointMap F G T i hi I e,
    ContinuousMulEquiv.apply_symm_apply]

/-- The section also recovers each actual positive point image. -/
@[simp] theorem logSection_characterLogHom_positivePointMap (a : intrinsicSubgroup F T) :
    logSection F G T i hi I e (characterLogHom F G (positivePointMap F G T i a)) =
      positivePointMap F G T i a := by
  rw [characterLogHom_positivePointMap F G T i hi I e, logSection_apply,
    ContinuousMulEquiv.symm_apply_apply]

include hi I e in
/-- The actual ambient logarithm is surjective under these supplied algebraic inputs. -/
theorem characterLog_surjective : Function.Surjective (characterLog F G) := by
  intro ℓ
  exact ⟨logSection F G T i hi I e (Multiplicative.ofAdd ℓ),
    characterLogHom_logSection F G T i hi I e (Multiplicative.ofAdd ℓ)⟩

include hi I e in
/-- The actual positive point map is injective, without an ambient embedding assumption. -/
theorem positivePointMap_injective : Function.Injective (positivePointMap F G T i) := by
  intro a b h
  apply (positiveAmbientLogEquiv F G T i hi I e).injective
  rw [← characterLogHom_positivePointMap F G T i hi I e,
    ← characterLogHom_positivePointMap F G T i hi I e, h]

/-- The section has precisely the existing intrinsic positive-torus image as its range. -/
theorem logSection_range :
    (logSection F G T i hi I e).toMonoidHom.range = imageSubgroup F T G i := by
  ext x
  constructor
  · rintro ⟨ℓ, rfl⟩
    exact ⟨_, ((positiveAmbientLogEquiv F G T i hi I e).symm ℓ).property, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨positiveAmbientLogEquiv F G T i hi I e ⟨a, ha⟩, ?_⟩
    change positivePointMap F G T i
      ((positiveAmbientLogEquiv F G T i hi I e).symm
        (positiveAmbientLogEquiv F G T i hi I e ⟨a, ha⟩)) = _
    rw [ContinuousMulEquiv.symm_apply_apply]
    rfl

include hi I e in
/-- An actual positive image point is norm one exactly when it is the identity. -/
theorem positiveImage_mem_normOne_iff {x : AdelicGroupPoints F G}
    (hx : x ∈ imageSubgroup F T G i) : x ∈ normOneSubgroup F G ↔ x = 1 := by
  rw [← logSection_range F G T i hi I e] at hx
  rcases hx with ⟨ℓ, rfl⟩
  constructor
  · intro h
    have hl : ℓ = 1 := by
      rw [← characterLogHom_logSection F G T i hi I e ℓ]
      exact (characterLog_eq_zero_iff F G _).mpr h
    rw [hl, map_one]
  · intro hx
    rw [hx]
    exact (normOneSubgroup F G).one_mem

include hi I e in
/-- The positive image and the actual norm-one subgroup have trivial intersection. -/
theorem positiveImage_inf_normOne :
    imageSubgroup F T G i ⊓ normOneSubgroup F G = ⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨hx, hn⟩
  exact (positiveImage_mem_normOne_iff F G T i hi I e hx).mp hn

end Langlands.Global.PositiveRealTorus
