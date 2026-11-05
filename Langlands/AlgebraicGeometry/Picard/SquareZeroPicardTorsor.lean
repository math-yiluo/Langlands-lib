import Langlands.AlgebraicGeometry.Picard.SquareZeroPicardNaturality
import Mathlib.Algebra.Torsor.Defs

/-! # Canonical torsor structure on actual square-zero Picard lifting fibres -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.SquareZeroPicardTorsor

open SquareZeroUnitCohomology SquareZeroPicardObstruction SquareZeroPicardFibres
open SquareZeroPicardNaturality

variable {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
  (i : Y ⟶ X) [IsClosedImmersion i] (hi : i.ker ^ 2 = ⊥)

/-- The unchanged actual Picard lifting fibre, with no chosen lift. -/
abbrev fibre (y : Group Y) := {x : Group X // Group.pullback i x = y}

/-- A deformation class acts by adding its actual ambient Picard class. -/
def fibreTranslate (y : Group Y) (q : infinitesimalClasses i hi) (x : fibre i y) :
    fibre i y :=
  ⟨(infinitesimalClassesEquivKernel i hi q).val + x.val, by
    rw [map_add, (infinitesimalClassesEquivKernel i hi q).property, zero_add, x.property]⟩

/-- The action is defined even when the lifting fibre is empty. -/
instance fibreAddAction (y : Group Y) :
    AddAction (infinitesimalClasses i hi) (fibre i y) where
  vadd := fibreTranslate i hi y
  zero_vadd x := by
    apply Subtype.ext
    change (infinitesimalClassesEquivKernel i hi 0).val + x.val = x.val
    rw [map_zero]
    exact zero_add x.val
  add_vadd q q' x := by
    apply Subtype.ext
    change (infinitesimalClassesEquivKernel i hi (q + q')).val + x.val =
      (infinitesimalClassesEquivKernel i hi q).val +
        ((infinitesimalClassesEquivKernel i hi q').val + x.val)
    rw [map_add]
    exact add_assoc _ _ _

@[simp]
lemma coe_vadd (y : Group Y) (q : infinitesimalClasses i hi) (x : fibre i y) :
    (q +ᵥ x : fibre i y).val = (infinitesimalClassesEquivKernel i hi q).val + x.val :=
  rfl

@[simp]
lemma coe_vadd_mk (y : Group Y) (a : idealCohomology i 1) (x : fibre i y) :
    ((QuotientAddGroup.mk a : infinitesimalClasses i hi) +ᵥ x : fibre i y).val =
      oneAddPicardMap i hi a + x.val := rfl

/-- The canonical difference is the quotient class of the actual Picard difference. -/
def fibreDifference (y : Group Y) (x x' : fibre i y) : infinitesimalClasses i hi :=
  (infinitesimalClassesEquivKernel i hi).symm
    ⟨x.val - x'.val, by
      change Group.pullback i (x.val - x'.val) = 0
      rw [map_sub, x.property, x'.property, sub_self]⟩

lemma fibreDifference_vadd (y : Group Y) (q : infinitesimalClasses i hi)
    (x : fibre i y) :
    fibreDifference i hi y (q +ᵥ x) x = q := by
  apply (infinitesimalClassesEquivKernel i hi).injective
  change (infinitesimalClassesEquivKernel i hi)
      ((infinitesimalClassesEquivKernel i hi).symm _) = _
  rw [AddEquiv.apply_symm_apply]
  apply Subtype.ext
  exact add_sub_cancel_right _ _

lemma fibreDifference_vadd_cancel (y : Group Y) (x x' : fibre i y) :
    fibreDifference i hi y x x' +ᵥ x' = x := by
  apply Subtype.ext
  change ((infinitesimalClassesEquivKernel i hi)
      ((infinitesimalClassesEquivKernel i hi).symm _)).val + x'.val = x.val
  rw [AddEquiv.apply_symm_apply]
  exact sub_add_cancel _ _

/-- Actual lifting fibres are nonempty exactly when the actual H² obstruction vanishes. -/
lemma fibre_nonempty_iff (y : Group Y) :
    Nonempty (fibre i y) ↔ obstructionMap i hi y = 0 := by
  rw [← picard_lift_iff i hi y]
  constructor
  · rintro ⟨x⟩
    exact ⟨x.val, x.property⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩

/-- Vanishing obstruction makes the actual fibre a torsor for actual deformation classes. -/
@[instance_reducible]
def fibreAddTorsor (y : Group Y) (hy : obstructionMap i hi y = 0) :
    AddTorsor (infinitesimalClasses i hi) (fibre i y) where
  toAddAction := fibreAddAction i hi y
  vsub := fibreDifference i hi y
  nonempty := (fibre_nonempty_iff i hi y).mpr hy
  vsub_vadd' := fibreDifference_vadd_cancel i hi y
  vadd_vsub' := fibreDifference_vadd i hi y

/-- The existing chosen-lift classifier is evaluation of the canonical action. -/
lemma infinitesimalClassesEquivFibre_eq_vadd (y : Group Y) (x : Group X)
    (hx : Group.pullback i x = y) (q : infinitesimalClasses i hi) :
    infinitesimalClassesEquivFibre i hi y x hx q =
      q +ᵥ (⟨x, hx⟩ : fibre i y) := rfl

/-- The existing chosen-lift classifier respects translation of deformation parameters. -/
lemma infinitesimalClassesEquivFibre_add (y : Group Y) (x : Group X)
    (hx : Group.pullback i x = y) (q q' : infinitesimalClasses i hi) :
    infinitesimalClassesEquivFibre i hi y x hx (q + q') =
      q +ᵥ infinitesimalClassesEquivFibre i hi y x hx q' :=
  add_vadd q q' (⟨x, hx⟩ : fibre i y)

/-- The inverse of the existing chosen-lift classifier is canonical difference. -/
lemma infinitesimalClassesEquivFibre_symm_eq_difference (y : Group Y)
    (x x' : fibre i y) :
    (infinitesimalClassesEquivFibre i hi y x'.val x'.property).symm x =
      fibreDifference i hi y x x' := rfl

variable {Z : Scheme.{u}} [CompactSpace Z] (j : Z ⟶ Y)
  [IsClosedImmersion (j ≫ i)] (hji : (j ≫ i).ker ^ 2 = ⊥)

/-- The actual map to the nested lifting fibre is equivariant for deformation classes. -/
lemma fibreMap_vadd (y : Group Y) (q : infinitesimalClasses i hi) (x : fibre i y) :
    fibreMap i j y (q +ᵥ x) =
      infinitesimalClassesMap i j hi hji q +ᵥ fibreMap i j y x := by
  apply Subtype.ext
  change (infinitesimalClassesEquivKernel i hi q).val + x.val =
    (infinitesimalClassesEquivKernel (j ≫ i) hji
      (infinitesimalClassesMap i j hi hji q)).val + x.val
  rw [infinitesimalClassesEquivKernel_naturality]
  rfl

/-- Canonical differences commute with the actual map to the nested lifting fibre. -/
lemma fibreDifference_fibreMap (y : Group Y) (x x' : fibre i y) :
    infinitesimalClassesMap i j hi hji (fibreDifference i hi y x x') =
      fibreDifference (j ≫ i) hji (Group.pullback j y)
        (fibreMap i j y x) (fibreMap i j y x') := by
  apply (infinitesimalClassesEquivKernel (j ≫ i) hji).injective
  rw [infinitesimalClassesEquivKernel_naturality]
  change pullbackKernelMap i j
      ((infinitesimalClassesEquivKernel i hi)
        ((infinitesimalClassesEquivKernel i hi).symm _)) =
    (infinitesimalClassesEquivKernel (j ≫ i) hji)
      ((infinitesimalClassesEquivKernel (j ≫ i) hji).symm _)
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  rfl

end Langlands.AlgebraicGeometry.Picard.SquareZeroPicardTorsor
