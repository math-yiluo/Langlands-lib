import Langlands.Global.RealSplitTorusIdentityComponent

/-! # Positive parameters for actual ordered-coefficient split-torus points -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Global.PositiveRealTorus

section OrderedUnits

variable (A : Type u) [Field A] [LinearOrder A] [IsStrictOrderedRing A]

/-- A positive unit lifted, with its original inverse, to the nonnegative subsemiring. -/
def positiveUnitLift (x : Aˣ) (hx : 0 < (x : A)) : (Nonneg A)ˣ where
  val := ⟨x.val, hx.le⟩
  inv := ⟨↑(x⁻¹), by simpa only [Units.val_inv_eq_inv_val] using (inv_pos.mpr hx).le⟩
  val_inv := Subtype.ext x.val_inv
  inv_val := Subtype.ext x.inv_val

@[simp] theorem positiveUnitMap_lift (x : Aˣ) (hx : 0 < (x : A)) :
    positiveUnitMap A (positiveUnitLift A x hx) = x := by
  apply Units.ext
  rfl

@[simp] theorem positiveUnitLift_map (x : (Nonneg A)ˣ) :
    positiveUnitLift A (positiveUnitMap A x)
      ((Nonneg.unitsEquivPos A x).property) = x := by
  apply Units.ext
  apply Subtype.ext
  rfl

variable [TopologicalSpace A]

/-- Positive units with their inherited subgroup topology are exactly nonnegative units. -/
def positiveUnitEquiv : (Nonneg A)ˣ ≃ₜ* Units.posSubgroup A where
  toFun x := ⟨positiveUnitMap A x, (Nonneg.unitsEquivPos A x).property⟩
  invFun x := positiveUnitLift A x.val x.property
  left_inv x := positiveUnitLift_map A x
  right_inv x := Subtype.ext (positiveUnitMap_lift A x.val x.property)
  map_mul' x y := Subtype.ext ((positiveUnitMap A).map_mul x y)
  continuous_toFun := (continuous_positiveUnitMap A).subtype_mk _
  continuous_invFun := Units.continuous_iff.mpr
    ⟨(Units.continuous_val.comp continuous_subtype_val).subtype_mk _,
      (Units.continuous_coe_inv.comp continuous_subtype_val).subtype_mk _⟩

@[simp] theorem positiveUnitEquiv_coe (x : (Nonneg A)ˣ) :
    (positiveUnitEquiv A x : Aˣ) = positiveUnitMap A x := rfl

@[simp] theorem positiveUnitMap_equiv_symm (x : Units.posSubgroup A) :
    positiveUnitMap A ((positiveUnitEquiv A).symm x) = x.val :=
  positiveUnitMap_lift A x.val x.property

end OrderedUnits

section ActualPoints

open Langlands.GroupScheme

variable (F : Type u) [Field F]
variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
variable (A : Type u) [Field A] [LinearOrder A] [IsStrictOrderedRing A] [Algebra F A]

/-- Character evaluation restricted to actual positive points and positive units. -/
def orderedCoefficientPositiveCharacter (χ : characterLattice T) :
    orderedCoefficientPositiveSubgroup F T A →* Units.posSubgroup A :=
  (characterHom F T A χ).restrict
    (fun x hx => (mem_orderedCoefficientPositiveSubgroup_iff F T A x).mp hx χ)

@[simp] theorem orderedCoefficientPositiveCharacter_coe
    (χ : characterLattice T) (x : orderedCoefficientPositiveSubgroup F T A) :
    (orderedCoefficientPositiveCharacter F T A χ x : Aˣ) =
      Lie.characterValue χ x.val := rfl

/-- Actual group-scheme morphisms preserve intrinsic coefficient positivity. -/
theorem pointMap_mem_orderedCoefficientPositiveSubgroup
    (T' : CommGroupScheme (Spec (CommRingCat.of F))) (f : T ⟶ T')
    (x : Lie.AffinePoints T.toGrp A)
    (hx : x ∈ orderedCoefficientPositiveSubgroup F T A) :
    pointMap F T.toGrp T'.toGrp A (CommGroupScheme.groupHom f) x ∈
      orderedCoefficientPositiveSubgroup F T' A := by
  apply (mem_orderedCoefficientPositiveSubgroup_iff F T' A _).mpr
  intro χ
  have h := (mem_orderedCoefficientPositiveSubgroup_iff F T A x).mp hx (f ≫ χ)
  rw [Lie.characterValue_comp] at h
  exact h

/-- The actual morphism restricted to the intrinsic positive subgroups. -/
def orderedCoefficientPositiveMap
    (T' : CommGroupScheme (Spec (CommRingCat.of F))) (f : T ⟶ T') :
    orderedCoefficientPositiveSubgroup F T A →*
      orderedCoefficientPositiveSubgroup F T' A :=
  (pointMap F T.toGrp T'.toGrp A (CommGroupScheme.groupHom f)).restrict
    (pointMap_mem_orderedCoefficientPositiveSubgroup F T A T' f)

@[simp] theorem orderedCoefficientPositiveMap_coe
    (T' : CommGroupScheme (Spec (CommRingCat.of F))) (f : T ⟶ T')
    (x : orderedCoefficientPositiveSubgroup F T A) :
    (orderedCoefficientPositiveMap F T A T' f x : Lie.AffinePoints T'.toGrp A) =
      pointMap F T.toGrp T'.toGrp A (CommGroupScheme.groupHom f) x.val := rfl

variable (I : Type u) [Fintype I]
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

/-- Positive parameters inserted into the actual split-torus point coordinates. -/
def orderedCoefficientFull : (I → (Nonneg A)ˣ) →* Lie.AffinePoints T.toGrp A :=
  (coordinates F I T e A).symm.toMonoidHom.comp ((positiveUnitMap A).compLeft I)

@[simp] theorem coordinates_orderedCoefficientFull (x : I → (Nonneg A)ˣ) :
    coordinates F I T e A (orderedCoefficientFull F T A I e x) =
      fun i => positiveUnitMap A (x i) :=
  (coordinates F I T e A).apply_symm_apply _

theorem orderedCoefficientFull_mem (x : I → (Nonneg A)ˣ) :
    orderedCoefficientFull F T A I e x ∈ orderedCoefficientPositiveSubgroup F T A := by
  rw [mem_orderedCoefficientPositiveSubgroup_iff_coordinates F T A I e,
    coordinates_orderedCoefficientFull]
  intro i
  exact (Nonneg.unitsEquivPos A (x i)).property

theorem characterValue_orderedCoefficientFull
    (χ : characterLattice T) (x : I → (Nonneg A)ˣ) :
    Lie.characterValue χ (orderedCoefficientFull F T A I e x) =
      positiveUnitMap A (∏ i, x i ^ characterExponents F I T e χ i) := by
  rw [characterValue_eq_prod F I T e χ, coordinates_orderedCoefficientFull]
  simp only [map_prod, map_zpow]

variable [TopologicalSpace A]

local instance positiveParametersAffinePointsTopology (G : GroupScheme (Spec (CommRingCat.of F))) :
    TopologicalSpace (Lie.AffinePoints G A) :=
  GroupScheme.affinePointsTopologicalSpace G (CommAlgCat.of F A)

/-- Positive coordinates, read from the actual point and lifted using its inverse. -/
def orderedCoefficientParameters (x : orderedCoefficientPositiveSubgroup F T A) :
    I → (Nonneg A)ˣ :=
  fun i => (positiveUnitEquiv A).symm
    ⟨coordinates F I T e A x.val i,
      (mem_orderedCoefficientPositiveSubgroup_iff_coordinates F T A I e x.val).mp
        x.property i⟩

@[simp] theorem positiveUnitMap_orderedCoefficientParameters
    (x : orderedCoefficientPositiveSubgroup F T A) (i : I) :
    positiveUnitMap A (orderedCoefficientParameters F T A I e x i) =
      coordinates F I T e A x.val i :=
  positiveUnitMap_equiv_symm A _

theorem continuous_orderedCoefficientParameters :
    Continuous (orderedCoefficientParameters F T A I e) := by
  apply continuous_pi
  intro i
  exact (positiveUnitEquiv A).symm.continuous.comp
    (((continuous_apply i).comp
      ((continuous_coordinates F I T e A).comp continuous_subtype_val)).subtype_mk _)

variable [IsTopologicalRing A]

theorem continuous_orderedCoefficientFull :
    Continuous (orderedCoefficientFull F T A I e) :=
  (continuous_coordinates_symm F I T e A).comp
    (continuous_pi fun i => (continuous_positiveUnitMap A).comp (continuous_apply i))

/-- The intrinsic positive subgroup has exactly the expected continuous group parameters. -/
def orderedCoefficientParameterEquiv :
    (I → (Nonneg A)ˣ) ≃ₜ* orderedCoefficientPositiveSubgroup F T A where
  toFun x := ⟨orderedCoefficientFull F T A I e x, orderedCoefficientFull_mem F T A I e x⟩
  invFun := orderedCoefficientParameters F T A I e
  left_inv x := by
    funext i
    apply (positiveUnitEquiv A).injective
    apply Subtype.ext
    rw [positiveUnitEquiv_coe, positiveUnitEquiv_coe,
      positiveUnitMap_orderedCoefficientParameters, coordinates_orderedCoefficientFull]
  right_inv x := by
    apply Subtype.ext
    apply (coordinates F I T e A).injective
    rw [coordinates_orderedCoefficientFull]
    funext i
    exact positiveUnitMap_orderedCoefficientParameters F T A I e x i
  map_mul' x y := Subtype.ext ((orderedCoefficientFull F T A I e).map_mul x y)
  continuous_toFun := (continuous_orderedCoefficientFull F T A I e).subtype_mk _
  continuous_invFun := continuous_orderedCoefficientParameters F T A I e

@[simp] theorem orderedCoefficientParameterEquiv_coe (x : I → (Nonneg A)ˣ) :
    (orderedCoefficientParameterEquiv F T A I e x : Lie.AffinePoints T.toGrp A) =
      orderedCoefficientFull F T A I e x := rfl

end ActualPoints

end Langlands.Global.PositiveRealTorus
