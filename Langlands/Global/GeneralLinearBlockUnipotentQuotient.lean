import Langlands.GroupScheme.GeneralLinearBlockUnipotentCoordinates
import Langlands.Global.AdelicSubgroupQuotient
import Langlands.Automorphic.ConstantTerm

/-! # The actual two-block unipotent rational quotient and the original matrix quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.Global.GeneralLinearBlockUnipotent

open Langlands.GeneralLinear

variable (F : Type u) [Field F] [NumberField F] {a b n : ℕ} (h : a + b = n)

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

/-- The existing subgroup functor with the actual original two-block numbering. -/
abbrev subgroup :=
  GroupScheme.GeneralLinear.blockUnipotent (Fin n) (CommRingCat.of F) (twoBlockWeight h)

/-- Coordinates on the actual rational subgroup points. No topology on `F` is chosen. -/
def rationalCoordinates :
    AdelicSubgroupPoints.rationalPoints F GLG (subgroup F h) ≃*
      Multiplicative (Matrix (Fin a) (Fin b) F) :=
  GroupScheme.GeneralLinear.twoBlockPointsEquiv h (CommRingCat.of F) (CommAlgCat.of F F)

/-- Coordinates on the actual full adelic subgroup points, with their inherited topology. -/
def adelicCoordinates :
    AdelicSubgroupPoints.adelicPoints F GLG (subgroup F h) ≃ₜ*
      Multiplicative (Matrix (Fin a) (Fin b) (Adeles F)) :=
  GroupScheme.GeneralLinear.twoBlockPointsHomeomorph h (CommRingCat.of F)
    (CommAlgCat.of F (Adeles F))

/-- Actual coefficient extension is the entrywise principal adele map in these coordinates. -/
theorem adelicCoordinates_rational
    (q : AdelicSubgroupPoints.rationalPoints F GLG (subgroup F h)) :
    (adelicCoordinates F h (AdelicSubgroupPoints.rational F GLG (subgroup F h) q)).toAdd =
      ((rationalCoordinates F h q).toAdd).map (diagonal F) := by
  change blockUnipotentCoordinates h
    (GeneralLinearGroupPoints.adelicEquiv F n
      (AdelicGroupPoints.rational F GLG q.val)) = _
  rw [GeneralLinearGroupPoints.adelicEquiv_rational]
  rfl

/-- Reducing the sum of a principal matrix and an adelic matrix discards the former. -/
theorem matrixQuotientMap_rational_add (C : Matrix (Fin a) (Fin b) F)
    (X : Matrix (Fin a) (Fin b) (Adeles F)) :
    matrixQuotientMap (C.map (diagonal F) + X) = matrixQuotientMap X := by
  ext i j
  change adeleQuotientMap F (diagonal F (C i j) + X i j) =
    adeleQuotientMap F (X i j)
  rw [map_add]
  have hz : adeleQuotientMap F (diagonal F (C i j)) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr ⟨C i j, rfl⟩
  rw [hz, zero_add]

theorem matrixQuotientMap_add (X Y : Matrix (Fin a) (Fin b) (Adeles F)) :
    matrixQuotientMap (X + Y) = matrixQuotientMap X + matrixQuotientMap Y := by
  ext i j
  exact map_add (adeleQuotientMap F) (X i j) (Y i j)

/-- Reduce the actual adelic subgroup coordinates modulo the actual principal image. -/
def quotientCoordinates :
    AdelicSubgroupPoints.RationalQuotient F GLG (subgroup F h) →
      Matrix (Fin a) (Fin b) (AdeleQuotient F) :=
  LeftCosetSpace.lift (AdelicSubgroupPoints.rationalSubgroup F GLG (subgroup F h))
    (fun x => matrixQuotientMap (adelicCoordinates F h x).toAdd) fun gamma x => by
      obtain ⟨q, hq⟩ := gamma.property
      change matrixQuotientMap (adelicCoordinates F h (gamma.val * x)).toAdd = _
      rw [map_mul]
      change matrixQuotientMap
        ((adelicCoordinates F h gamma.val).toAdd + (adelicCoordinates F h x).toAdd) = _
      rw [← hq, adelicCoordinates_rational, matrixQuotientMap_rational_add]

@[simp]
theorem quotientCoordinates_mk
    (x : AdelicSubgroupPoints.adelicPoints F GLG (subgroup F h)) :
    quotientCoordinates F h
      (LeftCosetSpace.mk (AdelicSubgroupPoints.rationalSubgroup F GLG (subgroup F h)) x) =
        matrixQuotientMap (adelicCoordinates F h x).toAdd := rfl

theorem quotientCoordinates_injective : Function.Injective (quotientCoordinates F h) := by
  intro x y
  induction x using Quotient.inductionOn with
  | _ x =>
    induction y using Quotient.inductionOn with
    | _ y =>
      intro hxy
      obtain ⟨C, hC⟩ := exists_rational_of_matrixQuotientMap_eq hxy
      let q := (rationalCoordinates F h).symm (Multiplicative.ofAdd C)
      have hy : y = AdelicSubgroupPoints.rational F GLG (subgroup F h) q * x := by
        apply (adelicCoordinates F h).injective
        rw [map_mul]
        change (adelicCoordinates F h y).toAdd =
          (adelicCoordinates F h
            (AdelicSubgroupPoints.rational F GLG (subgroup F h) q)).toAdd +
              (adelicCoordinates F h x).toAdd
        rw [adelicCoordinates_rational]
        simpa only [q, MulEquiv.apply_symm_apply, toAdd_ofAdd] using hC
      rw [hy]
      exact (LeftCosetSpace.mk_subgroup_mul
        (AdelicSubgroupPoints.rationalSubgroup F GLG (subgroup F h))
        ⟨AdelicSubgroupPoints.rational F GLG (subgroup F h) q, ⟨q, rfl⟩⟩ x).symm

theorem quotientCoordinates_surjective : Function.Surjective (quotientCoordinates F h) := by
  intro X
  refine ⟨LeftCosetSpace.mk
    (AdelicSubgroupPoints.rationalSubgroup F GLG (subgroup F h))
    ((adelicCoordinates F h).symm (Multiplicative.ofAdd (matrixLift X))), ?_⟩
  rw [quotientCoordinates_mk, (adelicCoordinates F h).apply_symm_apply]
  exact matrixQuotientMap_matrixLift X

/-- The actual rational quotient is the original matrix quotient, by an explicit bijection. -/
def quotientEquiv :
    AdelicSubgroupPoints.RationalQuotient F GLG (subgroup F h) ≃
      Matrix (Fin a) (Fin b) (AdeleQuotient F) :=
  Equiv.ofBijective (quotientCoordinates F h)
    ⟨quotientCoordinates_injective F h, quotientCoordinates_surjective F h⟩

@[simp]
theorem quotientEquiv_mk
    (x : AdelicSubgroupPoints.adelicPoints F GLG (subgroup F h)) :
    quotientEquiv F h
      (LeftCosetSpace.mk (AdelicSubgroupPoints.rationalSubgroup F GLG (subgroup F h)) x) =
        matrixQuotientMap (adelicCoordinates F h x).toAdd := rfl

theorem quotientEquiv_symm_matrixQuotientMap
    (X : Matrix (Fin a) (Fin b) (Adeles F)) :
    (quotientEquiv F h).symm (matrixQuotientMap X) =
      LeftCosetSpace.mk (AdelicSubgroupPoints.rationalSubgroup F GLG (subgroup F h))
        ((adelicCoordinates F h).symm (Multiplicative.ofAdd X)) := by
  apply (quotientEquiv F h).injective
  rw [Equiv.apply_symm_apply, quotientEquiv_mk,
    (adelicCoordinates F h).apply_symm_apply]
  rfl

/-- The quotient comparison preserves the actual quotient topologies in both directions. -/
def quotientHomeomorph :
    AdelicSubgroupPoints.RationalQuotient F GLG (subgroup F h) ≃ₜ
      Matrix (Fin a) (Fin b) (AdeleQuotient F) where
  toEquiv := quotientEquiv F h
  continuous_toFun := by
    apply (LeftCosetSpace.continuous_iff
      (AdelicSubgroupPoints.rationalSubgroup F GLG (subgroup F h))).mpr
    exact (isOpenQuotientMap_matrixQuotientMap (K := F) a b).continuous.comp
      (adelicCoordinates F h).continuous
  continuous_invFun := by
    apply (isOpenQuotientMap_matrixQuotientMap (K := F) a b).continuous_comp_iff.mp
    change Continuous ((quotientEquiv F h).symm ∘ matrixQuotientMap)
    have heq : (quotientEquiv F h).symm ∘ matrixQuotientMap =
        fun X => LeftCosetSpace.mk
          (AdelicSubgroupPoints.rationalSubgroup F GLG (subgroup F h))
          ((adelicCoordinates F h).symm (Multiplicative.ofAdd X)) :=
      funext (quotientEquiv_symm_matrixQuotientMap F h)
    rw [heq]
    exact (LeftCosetSpace.continuous_mk
      (AdelicSubgroupPoints.rationalSubgroup F GLG (subgroup F h))).comp
      (adelicCoordinates F h).symm.continuous

/-- Positive right translation becomes addition of the actual reduced matrix coordinates. -/
theorem quotientHomeomorph_rightTranslate
    (x : AdelicSubgroupPoints.adelicPoints F GLG (subgroup F h))
    (q : AdelicSubgroupPoints.RationalQuotient F GLG (subgroup F h)) :
    quotientHomeomorph F h
      (LeftCosetSpace.rightTranslate
        (AdelicSubgroupPoints.rationalSubgroup F GLG (subgroup F h)) x q) =
      quotientHomeomorph F h q + matrixQuotientMap (adelicCoordinates F h x).toAdd := by
  induction q using Quotient.inductionOn with
  | _ y =>
    change matrixQuotientMap (adelicCoordinates F h (y * x)).toAdd = _
    rw [map_mul]
    exact matrixQuotientMap_add F _ _

/-- Compactness is transported from the original additive adele quotient hypothesis. -/
instance rationalQuotientCompactSpace [CompactSpace (AdeleQuotient F)] :
    CompactSpace (AdelicSubgroupPoints.RationalQuotient F GLG (subgroup F h)) :=
  (quotientHomeomorph F h).symm.compactSpace

end Langlands.Global.GeneralLinearBlockUnipotent
