import Langlands.Global.PositiveRealTorusLog
import Langlands.GroupScheme.Rational.ProductDetection
import Langlands.GroupScheme.Reductive.CommutingMultiplication
import Mathlib.Algebra.Category.Grp.Injective

/-! # Lifting intrinsic positive points through surjective torus products -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (T A B : CommGroupScheme (Spec (CommRingCat.of F)))
  (j : A ⟶ T) (z : B ⟶ T)

/-- Every intrinsic positive point is the product of positive points in the
specified two source tori, through the actual morphisms. -/
def HasPositiveProductFactorization : Prop :=
  ∀ t : intrinsicSubgroup F T,
    ∃ (a : intrinsicSubgroup F A) (b : intrinsicSubgroup F B),
      map F A.toGrp T.toGrp (CommGroupScheme.groupHom j) a *
        map F B.toGrp T.toGrp (CommGroupScheme.groupHom z) b = t

/-- Joint injectivity on actual character lattices suffices for positive
product lifting. No integral splitting or rational-point lifting is used. -/
theorem hasPositiveProductFactorization_of_joint_character_injective
    (hT : IsSplitTorus T.toGrp) (hA : IsSplitTorus A.toGrp)
    (hB : IsSplitTorus B.toGrp)
    (hjoint : Function.Injective
      ((characterRestrict (CommGroupScheme.groupHom j)).prod
        (characterRestrict (CommGroupScheme.groupHom z)))) :
    HasPositiveProductFactorization F T A B j z := by
  classical
  obtain ⟨IT, hIT, ⟨eT⟩⟩ := hT
  obtain ⟨IA, hIA, ⟨eA⟩⟩ := hA
  obtain ⟨IB, hIB, ⟨eB⟩⟩ := hB
  let := hIT
  let := hIA
  let := hIB
  let : Fintype IT := Fintype.ofFinite IT
  let : Fintype IA := Fintype.ofFinite IA
  let : Fintype IB := Fintype.ofFinite IB
  intro t
  obtain ⟨L, hL⟩ := (Module.Baer.of_divisible ℝ).extension_property_addMonoidHom
    ((characterRestrict (CommGroupScheme.groupHom j)).prod
      (characterRestrict (CommGroupScheme.groupHom z))) hjoint
    (characterLog F T.toGrp t)
  let LA : RealCharacterDual F A.toGrp :=
    L.comp (AddMonoidHom.inl (characterLattice A) (characterLattice B))
  let LB : RealCharacterDual F B.toGrp :=
    L.comp (AddMonoidHom.inr (characterLattice A) (characterLattice B))
  let a := (positiveLogEquiv F A IA eA).symm (Multiplicative.ofAdd LA)
  let b := (positiveLogEquiv F B IB eB).symm (Multiplicative.ofAdd LB)
  have ha : characterLog F A.toGrp a = LA :=
    congrArg Multiplicative.toAdd ((positiveLogEquiv F A IA eA).apply_symm_apply _)
  have hb : characterLog F B.toGrp b = LB :=
    congrArg Multiplicative.toAdd ((positiveLogEquiv F B IB eB).apply_symm_apply _)
  have hpa : map F A.toGrp T.toGrp (CommGroupScheme.groupHom j) a ∈
      intrinsicSubgroup F T :=
    map_intrinsicSubgroup_le F A T j ⟨a, a.property, rfl⟩
  have hpb : map F B.toGrp T.toGrp (CommGroupScheme.groupHom z) b ∈
      intrinsicSubgroup F T :=
    map_intrinsicSubgroup_le F B T z ⟨b, b.property, rfl⟩
  let p : intrinsicSubgroup F T := ⟨_, (intrinsicSubgroup F T).mul_mem hpa hpb⟩
  have hp : positiveLogEquiv F T IT eT p = positiveLogEquiv F T IT eT t := by
    apply Multiplicative.toAdd.injective
    change characterLog F T.toGrp p = characterLog F T.toGrp t
    change characterLog F T.toGrp
      (map F A.toGrp T.toGrp (CommGroupScheme.groupHom j) a *
        map F B.toGrp T.toGrp (CommGroupScheme.groupHom z) b) = _
    rw [characterLog_mul, characterLog_map, characterLog_map, ha, hb]
    apply AddMonoidHom.ext
    intro χ
    change L (characterRestrict (CommGroupScheme.groupHom j) χ, 0) +
      L (0, characterRestrict (CommGroupScheme.groupHom z) χ) =
        characterLog F T.toGrp t χ
    rw [← map_add]
    simpa only [Prod.mk_add_mk, add_zero, zero_add,
      AddMonoidHom.comp_apply, AddMonoidHom.prod_apply] using DFunLike.congr_fun hL χ
  exact ⟨a, b, congrArg Subtype.val ((positiveLogEquiv F T IT eT).injective hp)⟩

omit [NumberField F] in
/-- Epimorphic multiplication detects actual torus characters jointly. -/
theorem joint_characterRestrict_injective_of_epi_product
    [Epi (subgroupProductMap (CommGroupScheme.groupHom j)
      (CommGroupScheme.groupHom z))] :
    Function.Injective
      ((characterRestrict (CommGroupScheme.groupHom j)).prod
        (characterRestrict (CommGroupScheme.groupHom z))) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro χ hχ
  have hj : characterRestrict (CommGroupScheme.groupHom j) χ = 0 :=
    congrArg Prod.fst hχ
  have hz : characterRestrict (CommGroupScheme.groupHom z) χ = 0 :=
    congrArg Prod.snd hχ
  exact congrArg Additive.ofMul
    (comp_eq_one_of_epi_subgroupProductMap
      (CommGroupScheme.groupHom j) (CommGroupScheme.groupHom z) χ.toMul
      (congrArg Additive.toMul hj) (congrArg Additive.toMul hz))

/-- Actual scheme-surjectivity of a product of split tori supplies positive
product factorization, even when the product has a finite or larger kernel. -/
theorem hasPositiveProductFactorization_of_surjective_product
    (hT : IsSplitTorus T.toGrp) (hA : IsSplitTorus A.toGrp)
    (hB : IsSplitTorus B.toGrp)
    (hsurj : Surjective (subgroupProductMap (CommGroupScheme.groupHom j)
      (CommGroupScheme.groupHom z)).left) :
    HasPositiveProductFactorization F T A B j z := by
  let : Smooth T.toGrp.X.hom := hT.smooth
  let : Smooth A.toGrp.X.hom := hA.smooth
  let : IsAffineHom A.toGrp.X.hom := hA.isAffineHom
  let : Smooth B.toGrp.X.hom := hB.smooth
  let : IsAffineHom B.toGrp.X.hom := hB.isAffineHom
  let : Surjective (subgroupProductMap (CommGroupScheme.groupHom j)
    (CommGroupScheme.groupHom z)).left := hsurj
  let : Flat (subgroupProductMap (CommGroupScheme.groupHom j)
    (CommGroupScheme.groupHom z)).left :=
    subgroupMultiplication_flat_of_surjective
      (CommGroupScheme.groupHom j) (CommGroupScheme.groupHom z)
      (fun _ _ _ => Commute.all _ _) hsurj
  let : Epi (subgroupProductMap (CommGroupScheme.groupHom j)
    (CommGroupScheme.groupHom z)).left := Flat.epi_of_flat_of_surjective _
  let : Epi (subgroupProductMap (CommGroupScheme.groupHom j)
    (CommGroupScheme.groupHom z)) := Over.epi_of_epi_left _
  exact hasPositiveProductFactorization_of_joint_character_injective F T A B j z
    hT hA hB (joint_characterRestrict_injective_of_epi_product F T A B j z)

end Langlands.Global.PositiveRealTorus
