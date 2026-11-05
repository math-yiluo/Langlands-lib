import Langlands.AlgebraicGeometry.Deformation.ElementaryKernelSubspaceQuotient
import Langlands.AlgebraicGeometry.Picard.ArtinianPicardObstructionFinite
import Langlands.AlgebraicGeometry.Picard.StructureKernelComposition

/-! # Actual ideal and cohomology maps for an elementary kernel quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianKernelQuotient

open Langlands.AlgebraicGeometry.Deformation
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open ArtinianTest ArtinianTest.ElementaryKernel
open ArtinianPicardObstructionFinite
open StructureKernelModule

private def factorizationIdealMap {T Y Z : Scheme.{u}}
    (j : Z ⟶ Y) (h : Y ⟶ T) {i : Z ⟶ T} (w : j ≫ h = i) :
    kernelModule i ⟶ (Scheme.Modules.pushforward h).obj (kernelModule j) :=
  eqToHom (congrArg kernelModule w.symm) ≫ compositionMap j h

private lemma factorizationIdealMap_app {T Y Z : Scheme.{u}}
    (j : Z ⟶ Y) (h : Y ⟶ T) {i : Z ⟶ T} (w : j ≫ h = i)
    (U : T.Opens) (a : Γ(kernelModule i, U)) :
    ((factorizationIdealMap j h w).app U a).val = h.app U a.val := by
  cases w
  rfl

private lemma factorizationIdealMap_ι {T Y Z : Scheme.{u}}
    (j : Z ⟶ Y) (h : Y ⟶ T) {i : Z ⟶ T} (w : j ≫ h = i) :
    factorizationIdealMap j h w ≫
        (Scheme.Modules.pushforward h).map (kernelModuleι j) =
      kernelModuleι i ≫ Langlands.Scheme.Modules.unitToPushforwardUnit h := by
  cases w
  exact compositionMap_ι j h

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  {A B : ArtinianTest k K} (q : A ⟶ B)
  [he : Fact (IsElementarySurjection q)]

local notation "hq" => he.out

local instance : Module K (Kernel q) := ElementaryKernel.residueModule q hq

variable (W : Submodule K (Kernel q))

local notation "AQ" => ElementaryKernelSubspaceQuotient.test q W
local notation "π" => ElementaryKernelSubspaceQuotient.projection q W
local notation "r" => ElementaryKernelSubspaceQuotient.reduction q W
local notation "h" => CategoryTheory.Functor.map (relativeSpace f) (ArtinianTest.baseMap π)
local notation "j" => CategoryTheory.Functor.map (relativeSpace f) (ArtinianTest.baseMap r)
local notation "pA" => NatTrans.app (relativeProjection f) (ArtinianTest.base A)
local notation "pQ" => NatTrans.app (relativeProjection f) (ArtinianTest.base AQ)
local notation "φ" => AlgHom.toRingHom (ArtinianTest.toAlgHom π)

/-- The actual relative maps compose to the original elementary immersion. -/
lemma factorization :
    j ≫ h = (relativeSpace f).map (ArtinianTest.baseMap q) := by
  rw [← Functor.map_comp, ArtinianTest.baseMap_comp,
    ElementaryKernelSubspaceQuotient.projection_reduction]

/-- The actual map of ideal modules induced by quotienting the kernel subspace. -/
def idealMap :
    idealModule f q ⟶ (Scheme.Modules.pushforward h).obj (idealModule f r) :=
  factorizationIdealMap j h (factorization f q W)

/-- On sections the quotient ideal map is the actual intermediate structure map. -/
@[simp]
lemma idealMap_app (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens)
    (a : Γ(idealModule f q, U)) :
    ((idealMap f q W).app U a).val = (h).app U a.val := by
  exact factorizationIdealMap_app j h (factorization f q W) U a

/-- The ideal quotient map commutes with the actual inclusions into the structure modules. -/
@[reassoc]
lemma idealMap_ι :
    idealMap f q W ≫ (Scheme.Modules.pushforward h).map (kernelModuleι j) =
      kernelModuleι ((relativeSpace f).map (ArtinianTest.baseMap q)) ≫
        Langlands.Scheme.Modules.unitToPushforwardUnit h :=
  factorizationIdealMap_ι j h (factorization f q W)

/-- The base scalars in the quotient comparison are the specified quotient ring map. -/
lemma projection_square :
    h ≫ pA = pQ ≫ Spec.map (CommRingCat.ofHom φ) :=
  (relativeProjection f).naturality (ArtinianTest.baseMap π)

/-- The actual source-ring-linear relative cohomology map for the quotient ideal. -/
def relativeCohomologyMap (n : ℕ) :
    (relativeCohomology pA n).obj (idealModule f q) ⟶
      (ModuleCat.restrictScalars φ).obj
        ((relativeCohomology pQ n).obj (idealModule f r)) := by
  letI : IsClosedImmersion h :=
    ArtinianSquareZeroPicardLifting.relativeMap_isClosedImmersion f π
      (ElementaryKernelSubspaceQuotient.projection_elementary q W).1
  letI : IsClosedImmersion j :=
    ArtinianSquareZeroPicardLifting.relativeMap_isClosedImmersion f r
      (ElementaryKernelSubspaceQuotient.reduction_elementary q W).1
  letI : (idealModule f r).IsQuasicoherent := kernelModule_isQuasicoherent j
  exact (relativeCohomology pA n).map (idealMap f q W) ≫
    (affinePushforwardCohomologyIso h pA (idealModule f r) n).inv ≫
    (relativeCohomologyBaseRingIso (CommRingCat.ofHom φ) (h ≫ pA) pQ
      (projection_square f q W) n).hom.app (idealModule f r)

attribute [local instance] ArtinianPicardObstructionFinite.sourceModule

/-- The quotient map on the unchanged ideal-cohomology groups, with original source scalars. -/
def cohomologySemilinearMap (n : ℕ) :
    Cohomology f q n →ₛₗ[φ] Cohomology f r n where
  toFun x := (relativeEquiv f r n).symm
    (relativeCohomologyMap f q W n (relativeEquiv f q n x))
  map_add' x y := by
    simp only [map_add]
  map_smul' a x := by
    change (relativeEquiv f r n).symm
      (relativeCohomologyMap f q W n (relativeEquiv f q n (a • x))) = _
    rw [map_smul, map_smul]
    exact (relativeEquiv f r n).symm.map_smul (φ a) _

variable [IsProper f]

/-- The actual quotient cohomology map is linear for the previously descended field actions. -/
def cohomologyLinearMap (n : ℕ) :
    letI := ArtinianPicardObstructionFinite.residueModule f q hq n
    letI := ArtinianPicardObstructionFinite.residueModule f r
      (ElementaryKernelSubspaceQuotient.reduction_elementary q W) n
    Cohomology f q n →ₗ[K] Cohomology f r n := by
  letI := ArtinianPicardObstructionFinite.residueModule f q hq n
  letI := ArtinianPicardObstructionFinite.residueModule f r
    (ElementaryKernelSubspaceQuotient.reduction_elementary q W) n
  refine { (cohomologySemilinearMap f q W n).toAddMonoidHom with map_smul' := ?_ }
  intro c x
  change cohomologySemilinearMap f q W n (c • x) =
    c • cohomologySemilinearMap f q W n x
  obtain ⟨a, rfl⟩ := A.augmentation_surjective c
  rw [ArtinianPicardObstructionFinite.augmentation_smul f q hq n,
    (cohomologySemilinearMap f q W n).map_smulₛₗ]
  have ha : A.augmentation a = (AQ).augmentation (φ a) := rfl
  rw [ha, ArtinianPicardObstructionFinite.augmentation_smul f r
    (ElementaryKernelSubspaceQuotient.reduction_elementary q W) n]

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianKernelQuotient
