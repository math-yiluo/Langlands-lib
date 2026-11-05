import Langlands.AlgebraicGeometry.Modules.ClosedImmersionCohomologyMap
import Langlands.AlgebraicGeometry.Picard.ArtinianKernelQuotientSheaf
import Langlands.AlgebraicGeometry.Picard.ArtinianResidueCohomology

/-! # Actual cohomology compatibility for an elementary kernel quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianKernelQuotientCohomology

open Langlands.AlgebraicGeometry.Deformation
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open ArtinianTest ArtinianTest.ElementaryKernel
open ArtinianPicardObstructionFinite ArtinianKernelQuotient
open ArtinianResidueSheaf ArtinianResidueCohomology ArtinianKernelQuotientSheaf

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
local notation "pA" => NatTrans.app (relativeProjection f) (ArtinianTest.base A)
local notation "pQ" => NatTrans.app (relativeProjection f) (ArtinianTest.base AQ)
local notation "φ" => CommRingCat.ofHom (AlgHom.toRingHom (ArtinianTest.toAlgHom π))

local instance : Fact (IsElementarySurjection r) :=
  ⟨ElementaryKernelSubspaceQuotient.reduction_elementary q W⟩
local instance : Module K (Kernel r) :=
  ElementaryKernel.residueModule r
    (ElementaryKernelSubspaceQuotient.reduction_elementary q W)
local instance : IsClosedImmersion h :=
  ArtinianSquareZeroPicardLifting.relativeMap_isClosedImmersion f π
    (ElementaryKernelSubspaceQuotient.projection_elementary q W).1

/-- The existing ideal-cohomology map is the actual closed-immersion map. -/
lemma relativeCohomologyMap_eq (n : ℕ) :
    relativeCohomologyMap f q W n =
      closedImmersionCohomologyMap φ pA pQ h (projection_square f q W)
        (idealMap f q W) n := by
  rfl

variable {ι κ : Type u} [Finite ι] [Finite κ]
  (b : Module.Basis ι K (Kernel q))
  (c : Module.Basis κ K
    (Kernel (ElementaryKernelSubspaceQuotient.reduction q W)))

/-- The actual quotient coefficient sheaf induces this relative cohomology map. -/
def quotientProductCohomologyMap (n : ℕ) :
    (relativeCohomology pA n).obj (residueProductModule f (A := A) ι) ⟶
      (ModuleCat.restrictScalars (φ).hom).obj
        ((relativeCohomology pQ n).obj (residueProductModule f (A := AQ) κ)) :=
  closedImmersionCohomologyMap φ pA pQ h (projection_square f q W)
    (quotientProductMap f q W b c) n

variable [Flat f]

/-- The actual ideal and coefficient quotient maps give the same cohomology square. -/
@[reassoc]
lemma productToIdeal_relativeCohomologyMap (n : ℕ) :
    (relativeCohomology pA n).map (productToIdeal f q b) ≫
        relativeCohomologyMap f q W n =
      quotientProductCohomologyMap f q W b c n ≫
        (ModuleCat.restrictScalars (φ).hom).map
          ((relativeCohomology pQ n).map (productToIdeal f r c)) := by
  rw [relativeCohomologyMap_eq]
  exact closedImmersionCohomologyMap_naturality φ pA pQ h
    (projection_square f q W) (quotientProductMap f q W b c)
    (idealMap f q W) (productToIdeal f q b) (productToIdeal f r c)
    (productToIdeal_quotient f q W b c) n

attribute [local instance] ArtinianPicardObstructionFinite.sourceModule

/-- Present unchanged ideal cohomology by the actual finite product sheaf. -/
def productCohomologyEquiv (n : ℕ) :
    Cohomology f q n ≃ₗ[A.algebra]
      (relativeCohomology pA n).obj (residueProductModule f (A := A) ι) :=
  (relativeEquiv f q n).trans
    ((relativeCohomology pA n).mapIso (residueProductIdealIso f q b).symm).toLinearEquiv

lemma productToIdeal_productCohomologyEquiv (n : ℕ) (x : Cohomology f q n) :
    (relativeCohomology pA n).map (productToIdeal f q b)
        (productCohomologyEquiv f q b n x) =
      relativeEquiv f q n x := by
  change (relativeCohomology pA n).map (residueProductIdealIso f q b).hom
      ((relativeCohomology pA n).map (residueProductIdealIso f q b).inv
        (relativeEquiv f q n x)) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

/-- The presentation of unchanged ideal cohomology carries the quotient to its
independently constructed coefficient-sheaf cohomology map. -/
lemma productCohomologyEquiv_quotient (n : ℕ) (x : Cohomology f q n) :
    productCohomologyEquiv f r c n (cohomologySemilinearMap f q W n x) =
      quotientProductCohomologyMap f q W b c n
        (productCohomologyEquiv f q b n x) := by
  apply ((relativeCohomology pQ n).mapIso (residueProductIdealIso f r c)).toLinearEquiv.injective
  have hs := congrArg
    (fun a => a (productCohomologyEquiv f q b n x))
    (productToIdeal_relativeCohomologyMap f q W b c n)
  change relativeCohomologyMap f q W n
      ((relativeCohomology pA n).map (productToIdeal f q b)
        (productCohomologyEquiv f q b n x)) =
    (relativeCohomology pQ n).map (productToIdeal f r c)
      (quotientProductCohomologyMap f q W b c n
        (productCohomologyEquiv f q b n x)) at hs
  rw [productToIdeal_productCohomologyEquiv] at hs
  change (relativeCohomology pQ n).map (productToIdeal f r c)
      (productCohomologyEquiv f r c n (cohomologySemilinearMap f q W n x)) = _
  rw [productToIdeal_productCohomologyEquiv]
  change (relativeEquiv f r n) ((relativeEquiv f r n).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  exact hs

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianKernelQuotientCohomology
