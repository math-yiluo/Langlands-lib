import Langlands.AlgebraicGeometry.Picard.ArtinianKernelQuotientCohomologyCoordinates

/-! # Tensor naturality of the actual elementary ideal cohomology quotient -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianKernelQuotientTensorNaturality

open Langlands.AlgebraicGeometry.Deformation
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open ArtinianTest ArtinianTest.ElementaryKernel
open ArtinianPicardObstructionFinite ArtinianKernelQuotient
open ArtinianResidueSheaf ArtinianResidueCohomology
open ArtinianKernelQuotientCohomology ArtinianKernelQuotientCoordinates
open ArtinianKernelQuotientCohomologyCoordinates

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  {A B : ArtinianTest k K} (q : A ⟶ B)
  [he : Fact (IsElementarySurjection q)]

local notation "hq" => he.out
local instance : Module K (Kernel q) := ElementaryKernel.residueModule q hq
variable (W : Submodule K (Kernel q))

local notation "AQ" => ElementaryKernelSubspaceQuotient.test q W
local notation "r" => ElementaryKernelSubspaceQuotient.reduction q W

local instance : Fact (IsElementarySurjection r) :=
  ⟨ElementaryKernelSubspaceQuotient.reduction_elementary q W⟩
local instance : Module K (Kernel r) :=
  ElementaryKernel.residueModule r
    (ElementaryKernelSubspaceQuotient.reduction_elementary q W)

/-- The identity on actual residue cohomology tensored with the actual kernel quotient. -/
def residueCohomologyTensorQuotientMap (n : ℕ) :
    ResidueCohomology (K := K) f n ⊗[K] Kernel q →ₗ[K]
      ResidueCohomology (K := K) f n ⊗[K] Kernel r :=
  TensorProduct.map LinearMap.id (ElementaryKernelSubspaceQuotient.kernelLinearMap q W)

variable {ι κ : Type u} [Finite ι] [Finite κ]
  (b : Module.Basis ι K (Kernel q))
  (c : Module.Basis κ K
    (Kernel (ElementaryKernelSubspaceQuotient.reduction q W)))

local instance : Fintype ι := Fintype.ofFinite ι

/-- The actual tensor quotient has the same finite coefficient formula. -/
lemma residueCohomologyTensorQuotientMap_coordinates (n : ℕ)
    (t : ResidueCohomology (K := K) f n ⊗[K] Kernel q) (l : κ) :
    vectorTensorCoordinates c (residueCohomologyTensorQuotientMap f q W n t) l =
      ∑ j, kernelQuotientMatrix q W b c l j • vectorTensorCoordinates b t j := by
  exact vectorTensorCoordinates_map b c
    (ElementaryKernelSubspaceQuotient.kernelLinearMap q W) LinearMap.id t l

variable [Flat f]

attribute [local instance] ArtinianPicardObstructionFinite.sourceModule

/-- The independent ideal-cohomology coordinates are the residue-product coordinates
of its existing product-sheaf presentation. -/
lemma residueProductCohomologyCoordinates_productCohomologyEquiv (n : ℕ)
    (x : Cohomology f q n) :
    residueProductCohomologyCoordinates f A ι n (productCohomologyEquiv f q b n x) =
      idealCohomologyCoordinates f q b n x := rfl

/-- The independently constructed quotient map on actual ideal cohomology
has the coefficient formula of the actual kernel quotient. -/
lemma idealCohomologyCoordinates_quotient (n : ℕ) (x : Cohomology f q n) (l : κ) :
    idealCohomologyCoordinates f r c n (cohomologySemilinearMap f q W n x) l =
      ∑ j, kernelQuotientMatrix q W b c l j •
        (show ResidueCohomology (K := K) f n from idealCohomologyCoordinates f q b n x j) := by
  rw [← residueProductCohomologyCoordinates_productCohomologyEquiv,
    productCohomologyEquiv_quotient f q W b c n x]
  have ht := quotientProductCohomologyMap_coordinates f q W b c n
    (productCohomologyEquiv f q b n x) l
  simpa only [residueProductCohomologyCoordinates_productCohomologyEquiv] using ht

variable [IsProper f]

/-- Tensor coordinates of the actual ideal comparison are its independently
constructed cohomology coordinates. -/
lemma vectorTensorCoordinates_idealCohomologyTensorEquiv (n : ℕ)
    (x : Cohomology f q n) :
    letI := ArtinianPicardObstructionFinite.residueModule f q hq n
    vectorTensorCoordinates b (idealCohomologyTensorEquiv f q b n x) =
      idealResidueCohomologyCoordinates f q b n x := by
  let := ArtinianPicardObstructionFinite.residueModule f q hq n
  change vectorTensorCoordinates b ((vectorTensorCoordinates b).symm _) = _
  exact (vectorTensorCoordinates b).apply_symm_apply _

/-- The actual ideal quotient agrees with identity on residue cohomology tensored
with the actual kernel quotient under the existing tensor equivalences. -/
lemma idealCohomologyTensorEquiv_quotient (n : ℕ) :
    letI := ArtinianPicardObstructionFinite.residueModule f q hq n
    letI := ArtinianPicardObstructionFinite.residueModule f r
      (ElementaryKernelSubspaceQuotient.reduction_elementary q W) n
    ∀ x : Cohomology f q n,
      idealCohomologyTensorEquiv f r c n (cohomologyLinearMap f q W n x) =
        residueCohomologyTensorQuotientMap f q W n
          (idealCohomologyTensorEquiv f q b n x) := by
  let := ArtinianPicardObstructionFinite.residueModule f q hq n
  let := ArtinianPicardObstructionFinite.residueModule f r
    (ElementaryKernelSubspaceQuotient.reduction_elementary q W) n
  intro x
  apply (vectorTensorCoordinates c).injective
  ext l
  rw [residueCohomologyTensorQuotientMap_coordinates f q W b c,
    vectorTensorCoordinates_idealCohomologyTensorEquiv,
    vectorTensorCoordinates_idealCohomologyTensorEquiv]
  change idealCohomologyCoordinates f r c n (cohomologySemilinearMap f q W n x) l =
    ∑ j, kernelQuotientMatrix q W b c l j •
      (show ResidueCohomology (K := K) f n from idealCohomologyCoordinates f q b n x j)
  exact idealCohomologyCoordinates_quotient f q W b c n x l

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianKernelQuotientTensorNaturality
