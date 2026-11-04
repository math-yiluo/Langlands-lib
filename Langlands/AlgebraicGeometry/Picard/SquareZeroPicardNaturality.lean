import Langlands.AlgebraicGeometry.Picard.SquareZeroUnitNaturality
import Langlands.AlgebraicGeometry.Picard.SquareZeroPicardFibres
import Langlands.AlgebraicGeometry.Picard.Functor

/-! # Actual Picard deformation classes for nested square-zero thickenings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.SquareZeroPicardNaturality

open SquareZeroUnitCohomology SquareZeroUnitNaturality
open SquareZeroPicardObstruction SquareZeroPicardFibres

variable {X Y Z : Scheme.{u}} (i : Y ⟶ X) (j : Z ⟶ Y)

/-- The actual ambient Picard class gives an inclusion of the two pullback kernels. -/
def pullbackKernelMap : (Group.pullback i).ker →+ (Group.pullback (j ≫ i)).ker where
  toFun a := ⟨a.val, by
    change Group.pullback (j ≫ i) a.val = 0
    rw [Group.pullback_comp, AddMonoidHom.comp_apply, a.property, map_zero]⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma coe_pullbackKernelMap (a : (Group.pullback i).ker) :
    (pullbackKernelMap i j a : Group X) = a.val := rfl

lemma pullbackKernelMap_injective : Function.Injective (pullbackKernelMap i j) := by
  intro a b h
  exact Subtype.ext (congrArg (fun a : (Group.pullback (j ≫ i)).ker ↦ a.val) h)

/-- Keeping the ambient class gives a map to the fibre over its further pullback. -/
def fibreMap (y : Group Y) :
    {x : Group X // Group.pullback i x = y} →
      {x : Group X // Group.pullback (j ≫ i) x = Group.pullback j y} :=
  fun x ↦ ⟨x.val, by
    rw [Group.pullback_comp, AddMonoidHom.comp_apply, x.property]⟩

@[simp]
lemma coe_fibreMap (y : Group Y) (x : {x : Group X // Group.pullback i x = y}) :
    (fibreMap i j y x : Group X) = x.val := rfl

lemma fibreMap_injective (y : Group Y) : Function.Injective (fibreMap i j y) := by
  intro a b h
  exact Subtype.ext (congrArg
    (fun a : {x : Group X // Group.pullback (j ≫ i) x = Group.pullback j y} ↦ a.val) h)

variable [IsClosedImmersion i] [IsClosedImmersion (j ≫ i)]
  (hi : i.ker ^ 2 = ⊥) (hji : (j ≫ i).ker ^ 2 = ⊥)

/-- Actual degree-zero unit boundaries remain boundaries under ideal inclusion. -/
lemma boundaryImage_le :
    (boundaryMap i hi 0).range ≤
      ((boundaryMap (j ≫ i) hji 0).range).comap (idealCohomologyMap i j 1) := by
  rintro a ⟨y, rfl⟩
  exact ⟨quotientUnitCohomologyMap i j hi hji 0 y,
    boundaryMap_naturality i j hi hji 0 y⟩

/-- The actual ideal-cohomology map descends modulo the actual unit boundaries. -/
def infinitesimalClassesMap :
    infinitesimalClasses i hi →+ infinitesimalClasses (j ≫ i) hji :=
  QuotientAddGroup.map (boundaryMap i hi 0).range (boundaryMap (j ≫ i) hji 0).range
    (idealCohomologyMap i j 1) (boundaryImage_le i j hi hji)

@[simp]
lemma infinitesimalClassesMap_mk (a : idealCohomology i 1) :
    infinitesimalClassesMap i j hi hji (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (idealCohomologyMap i j 1 a) := rfl

variable [CompactSpace X]

/-- The actual Picard `1+a` maps commute with ideal inclusion. -/
lemma oneAddPicardMap_naturality (a : idealCohomology i 1) :
    oneAddPicardMap (j ≫ i) hji (idealCohomologyMap i j 1 a) =
      oneAddPicardMap i hi a := by
  apply (Group.unitCohomologyAddEquiv X).injective
  rw [cohomology_oneAddPicardMap, cohomology_oneAddPicardMap]
  exact oneAddMap_naturality i j hi hji 1 a

variable [CompactSpace Y] [CompactSpace Z]

/-- The published quotient/kernel classifiers intertwine the actual maps. -/
lemma infinitesimalClassesEquivKernel_naturality (q : infinitesimalClasses i hi) :
    infinitesimalClassesEquivKernel (j ≫ i) hji (infinitesimalClassesMap i j hi hji q) =
      pullbackKernelMap i j (infinitesimalClassesEquivKernel i hi q) := by
  refine QuotientAddGroup.induction_on q fun a ↦ ?_
  apply Subtype.ext
  change oneAddPicardMap (j ≫ i) hji (idealCohomologyMap i j 1 a) =
    oneAddPicardMap i hi a
  exact oneAddPicardMap_naturality i j hi hji a

/-- The induced map of actual deformation classes is injective. -/
lemma infinitesimalClassesMap_injective :
    Function.Injective (infinitesimalClassesMap i j hi hji) := by
  intro a b h
  apply (infinitesimalClassesEquivKernel i hi).injective
  apply pullbackKernelMap_injective i j
  rw [← infinitesimalClassesEquivKernel_naturality,
    ← infinitesimalClassesEquivKernel_naturality, h]

/-- Translation by the same lift intertwines the quotient map and actual fibre map. -/
lemma infinitesimalClassesEquivFibre_naturality
    (y : Group Y) (x : Group X) (hx : Group.pullback i x = y)
    (q : infinitesimalClasses i hi) :
    infinitesimalClassesEquivFibre (j ≫ i) hji (Group.pullback j y) x
        (by rw [Group.pullback_comp, AddMonoidHom.comp_apply, hx])
        (infinitesimalClassesMap i j hi hji q) =
      fibreMap i j y (infinitesimalClassesEquivFibre i hi y x hx q) := by
  apply Subtype.ext
  change (infinitesimalClassesEquivKernel (j ≫ i) hji
      (infinitesimalClassesMap i j hi hji q)).val + x =
    (infinitesimalClassesEquivKernel i hi q).val + x
  rw [infinitesimalClassesEquivKernel_naturality]
  rfl

end Langlands.AlgebraicGeometry.Picard.SquareZeroPicardNaturality
