import Langlands.Geometry.Building.ValuationBuildingData
import Langlands.Geometry.Building.KPApartmentAxioms
import Langlands.BruhatTits.RationalPoints.BoundedSubgroupNormKernel

/-!
# Singleton sharp-fixer boundedness and the actual centralizer norm kernel

The boundedness statement is a proof obligation. The supporting adapter proves
its consequence for the actual centralizer, conditional on that boundedness.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The singleton consequence of KP Corollary 7.3.14 needed for the centralizer
intersection argument, under the exact corrected apartment premise. -/
def SharpFixerBoundednessStatement : Prop :=
  B.apartment.SatisfiesApartmentAxioms B.centralizer →
    ∀ x : B.Apartment,
      IsAlgebraicallyBounded F G.X (B.sharpFixer {x} : Set (rationalPoints G))

/-- Boundedness of an actual singleton sharp fixer puts its pullback in the
actual centralizer's norm-one subgroup. -/
theorem comap_sharpFixer_le_centralizerNormKernel_of_isAlgebraicallyBounded
    (x : B.Apartment)
    (hbound : IsAlgebraicallyBounded F G.X
      (B.sharpFixer {x} : Set (rationalPoints G))) :
    (B.sharpFixer {x}).comap (rationalPoints.map B.centralizer.j) ≤
      rationalCommonNormKernel B.centralizer.Z := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  let : IsClosedImmersion B.centralizer.j.hom.hom.left :=
    B.centralizer.isClosedSubgroup
  let : IsAffine B.centralizer.Z.X.left :=
    isAffine_of_isAffineHom B.centralizer.j.hom.hom.left
  have : LocallyOfFiniteType B.centralizer.Z.X.hom := by
    rw [← B.centralizer.j.hom.hom.w]
    infer_instance
  exact comap_le_rationalCommonNormKernel_of_isAlgebraicallyBounded
    B.centralizer.j B.centralizer.isClosedSubgroup (B.sharpFixer {x}) hbound

/-- The boundedness proof obligation yields the actual centralizer norm-one
inclusion under the same apartment premise. -/
theorem comap_sharpFixer_le_centralizerNormKernel
    (hbound : B.SharpFixerBoundednessStatement)
    (hB : B.apartment.SatisfiesApartmentAxioms B.centralizer)
    (x : B.Apartment) :
    (B.sharpFixer {x}).comap (rationalPoints.map B.centralizer.j) ≤
      rationalCommonNormKernel B.centralizer.Z :=
  B.comap_sharpFixer_le_centralizerNormKernel_of_isAlgebraicallyBounded x (hbound hB x)

end Langlands.Geometry.Building.ValuationBuildingData
