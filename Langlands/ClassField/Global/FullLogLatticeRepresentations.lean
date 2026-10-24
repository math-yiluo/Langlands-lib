import Langlands.ClassField.Global.FullLogQuotientAction
import Langlands.ClassField.Global.InfinitePlaceCoordinateLattice

/-! # Representation comparisons for the two full logarithmic-coordinate lattices -/

noncomputable section

open NumberField CategoryTheory
open scoped Classical

namespace Langlands.ClassField.Global

universe u v

variable (F : Type u) [Field F] (E : Type v) [Field E] [NumberField E] [Algebra F E]

/-- The actual arithmetic representation on the augmented logarithmic unit lattice. -/
def augmentedFullLogUnitLatticeRepresentation :
    Rep.{v} NormalizedTwoCocycle.CoefficientScalars.{v} (E ≃ₐ[F] E) :=
  Rep.of
    { toFun g := (augmentedFullLogUnitLatticeAut F E g).toLinearMap.restrictScalars
        NormalizedTwoCocycle.CoefficientScalars.{v}
      map_one' := by ext x; simp
      map_mul' g h := by ext x; simp }

@[simp] theorem augmentedFullLogUnitLatticeRepresentation_apply (g : E ≃ₐ[F] E)
    (x : augmentedFullLogUnitLattice E) :
    (augmentedFullLogUnitLatticeRepresentation F E).ρ g x =
      augmentedFullLogUnitLatticeAut F E g x := rfl

/-- The actual arithmetic representation on the integer coordinate lattice. -/
def infinitePlaceCoordinateLatticeRepresentation :
    Rep.{v} NormalizedTwoCocycle.CoefficientScalars.{v} (E ≃ₐ[F] E) :=
  Rep.of
    { toFun g := (infinitePlaceCoordinateLatticeAut F E g).toLinearMap.restrictScalars
        NormalizedTwoCocycle.CoefficientScalars.{v}
      map_one' := by ext x; simp
      map_mul' g h := by ext x; simp }

@[simp] theorem infinitePlaceCoordinateLatticeRepresentation_apply (g : E ≃ₐ[F] E)
    (x : infinitePlaceCoordinateLattice E) :
    (infinitePlaceCoordinateLatticeRepresentation F E).ρ g x =
      infinitePlaceCoordinateLatticeAut F E g x := rfl

/-- The canonical infinite-place representation is its actual coordinate-lattice realization. -/
def infinitePlaceLatticeRealizationIso :
    infinitePlaceLatticeRepresentation F E ≅ infinitePlaceCoordinateLatticeRepresentation F E :=
  Rep.mkIso (.mk ((infinitePlaceLatticeRealization F E).restrictScalars
    NormalizedTwoCocycle.CoefficientScalars.{v}) (fun g => by
      apply LinearMap.ext
      intro x
      exact infinitePlaceLatticeRealization_equivariant F E g x))

@[simp] theorem infinitePlaceLatticeRealizationIso_apply
    (x : (infinitePlaceLatticeRepresentation F E).V) :
    (infinitePlaceLatticeRealizationIso F E).hom.hom x = infinitePlaceLatticeRealization F E x :=
  rfl

/-- The logarithmic unit lattice together with the trivial lifted-integer representation. -/
def fullLogUnitLatticeWithConstantsRepresentation :
    Rep.{v} NormalizedTwoCocycle.CoefficientScalars.{v} (E ≃ₐ[F] E) :=
  Rep.of ((fullLogUnitLatticeRepresentation F E).ρ.prod
    (Representation.trivial NormalizedTwoCocycle.CoefficientScalars.{v}
      (E ≃ₐ[F] E) NormalizedTwoCocycle.CoefficientScalars.{v}))

@[simp] theorem fullLogUnitLatticeWithConstantsRepresentation_apply (g : E ≃ₐ[F] E)
    (x : fullLogUnitLattice E × NormalizedTwoCocycle.CoefficientScalars.{v}) :
    (fullLogUnitLatticeWithConstantsRepresentation F E).ρ g x =
      (fullLogUnitLatticeAut F E g x.1, x.2) := rfl

/-- The integral splitting, with its integer coordinate lifted to the coefficient universe. -/
def fullLogIntegralSplitLifted :
    augmentedFullLogUnitLattice E ≃ₗ[NormalizedTwoCocycle.CoefficientScalars.{v}]
      (fullLogUnitLattice E × NormalizedTwoCocycle.CoefficientScalars.{v}) :=
  ((fullLogIntegralSplit E).trans
    ((LinearEquiv.refl ℤ (fullLogUnitLattice E)).prodCongr
      (ULift.moduleEquiv : NormalizedTwoCocycle.CoefficientScalars.{v} ≃ₗ[ℤ] ℤ).symm)).restrictScalars
        NormalizedTwoCocycle.CoefficientScalars.{v}

@[simp] theorem fullLogIntegralSplitLifted_apply (x : augmentedFullLogUnitLattice E) :
    fullLogIntegralSplitLifted E x =
      ((fullLogIntegralSplit E x).1, ULift.up (fullLogIntegralSplit E x).2) := rfl

/-- The augmented lattice splits equivariantly as its unit part and trivial integers. -/
def fullLogIntegralSplitRepresentationIso :
    augmentedFullLogUnitLatticeRepresentation F E ≅
      fullLogUnitLatticeWithConstantsRepresentation F E :=
  Rep.mkIso (.mk (fullLogIntegralSplitLifted E) (fun g => by
    apply LinearMap.ext
    intro x
    change fullLogIntegralSplitLifted E (augmentedFullLogUnitLatticeAut F E g x) =
      (fullLogUnitLatticeAut F E g (fullLogIntegralSplitLifted E x).1,
        (fullLogIntegralSplitLifted E x).2)
    simp only [fullLogIntegralSplitLifted_apply, fullLogIntegralSplit_equivariant]))

@[simp] theorem fullLogIntegralSplitRepresentationIso_apply (x : augmentedFullLogUnitLattice E) :
    (fullLogIntegralSplitRepresentationIso F E).hom.hom x = fullLogIntegralSplitLifted E x := rfl

/-- The coordinate-lattice realization induces ordinary cohomology isomorphisms. -/
def infinitePlaceLatticeRealizationCohomologyIso (n : ℕ) :
    groupCohomology (infinitePlaceLatticeRepresentation F E) n ≅
      groupCohomology (infinitePlaceCoordinateLatticeRepresentation F E) n :=
  (groupCohomology.functor NormalizedTwoCocycle.CoefficientScalars.{v}
    (E ≃ₐ[F] E) n).mapIso (infinitePlaceLatticeRealizationIso F E)

/-- The integral splitting induces ordinary cohomology isomorphisms. -/
def fullLogIntegralSplitCohomologyIso (n : ℕ) :
    groupCohomology (augmentedFullLogUnitLatticeRepresentation F E) n ≅
      groupCohomology (fullLogUnitLatticeWithConstantsRepresentation F E) n :=
  (groupCohomology.functor NormalizedTwoCocycle.CoefficientScalars.{v}
    (E ≃ₐ[F] E) n).mapIso (fullLogIntegralSplitRepresentationIso F E)

end Langlands.ClassField.Global
