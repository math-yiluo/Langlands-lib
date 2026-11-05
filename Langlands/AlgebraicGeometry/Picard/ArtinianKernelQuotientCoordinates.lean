import Langlands.AlgebraicGeometry.Picard.ArtinianResidueCohomologyQuotient

/-! # Finite coordinates for the actual elementary kernel quotient -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianKernelQuotientCoordinates

open Langlands.AlgebraicGeometry.Deformation
open ArtinianTest ArtinianTest.ElementaryKernel
open ArtinianPicardKernelTensor
open ArtinianPicardObstructionFinite ArtinianKernelQuotient
open ArtinianResidueSections ArtinianResidueSheaf ArtinianResidueCohomology
open ArtinianKernelQuotientResidue ArtinianKernelQuotientSheaf
open ArtinianResidueCohomologyQuotient

section LinearCoordinates

variable {K V V' ι κ : Type u} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
  (b : Module.Basis ι K V) (c : Module.Basis κ K V') (φ : V →ₗ[K] V')

/-- Coefficients of a linear map in two specified bases. -/
def coefficientMatrix : κ → ι → K := fun l j => c.repr (φ (b j)) l

variable [Fintype ι]

/-- Evaluation of a linear map is ordinary multiplication by its coefficient matrix. -/
lemma coefficientMatrix_apply (v : V) (l : κ) :
    c.repr (φ v) l = ∑ j, b.repr v j * coefficientMatrix b c φ l j := by
  calc
    _ = c.repr (φ (∑ j, b.repr v j • b j)) l := by rw [b.sum_repr]
    _ = _ := by
      simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
        smul_eq_mul, coefficientMatrix]

variable [Finite κ] {H H' : Type u}
  [AddCommGroup H] [Module K H] [AddCommGroup H'] [Module K H']
  (ψ : H →ₗ[K] H')

/-- Finite tensor coordinates turn both actual linear maps into the coefficient formula. -/
lemma vectorTensorCoordinates_map (t : H ⊗[K] V) (l : κ) :
    vectorTensorCoordinates c (TensorProduct.map ψ φ t) l =
      ∑ j, coefficientMatrix b c φ l j • ψ (vectorTensorCoordinates b t j) := by
  induction t using TensorProduct.inductionOn with
  | tmul x v =>
    simp only [TensorProduct.map_tmul, vectorTensorCoordinates_tmul, map_smul]
    rw [coefficientMatrix_apply b c φ v l, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [smul_smul, mul_comm]
  | add x y hx hy =>
    simpa only [map_add, LinearEquiv.map_add, Pi.add_apply, smul_add,
      Finset.sum_add_distrib] using congrArg₂ (· + ·) hx hy

variable {S T : Type u} [CommRing S] [Algebra K S]
  [CommRing T] [Algebra K T] (χ : S →ₐ[K] T)

/-- The same finite coefficient formula for scalar-extension tensor coordinates. -/
lemma tensorCoordinates_mapCoefficients (t : S ⊗[K] V) (l : κ) :
    tensorCoordinates c T (TensorProduct.map χ.toLinearMap φ t) l =
      ∑ j, coefficientMatrix b c φ l j • χ (tensorCoordinates b S t j) := by
  induction t using TensorProduct.inductionOn with
  | tmul x v =>
    simp only [TensorProduct.map_tmul, tensorCoordinates_tmul, AlgHom.toLinearMap_apply,
      map_smul]
    rw [coefficientMatrix_apply b c φ v l, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [smul_smul, mul_comm]
  | add x y hx hy =>
    simpa only [map_add, LinearEquiv.map_add, Pi.add_apply, smul_add,
      Finset.sum_add_distrib] using congrArg₂ (· + ·) hx hy

end LinearCoordinates

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
local notation "iA" => residueMap f A
local notation "iQ" => residueMap f AQ
local notation "XK" => CategoryTheory.Functor.obj (relativeSpace f) (ArtinianTest.residueBase k K)

local instance : Fact (IsElementarySurjection r) :=
  ⟨ElementaryKernelSubspaceQuotient.reduction_elementary q W⟩
local instance : Module K (Kernel r) :=
  ElementaryKernel.residueModule r
    (ElementaryKernelSubspaceQuotient.reduction_elementary q W)

attribute [local instance] sectionAlgebra
  residueSectionAlgebra ArtinianResidueKernel.residueSourceAlgebra

/-- The canonical pushforward identification is the actual restriction of residue sections. -/
lemma residueQuotientIso_app
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens)
    (s : Γ(XK, iA ⁻¹ᵁ U)) :
    (residueQuotientIso f q W).hom.app U s = quotientResidueSectionMap f q W U s := by
  change (((Scheme.Modules.pushforwardCongr
      (residue_factorization f q W).symm).hom.app
        (SheafOfModules.unit (XK).ringCatSheaf)).app U ≫
      ((Scheme.Modules.pushforwardComp iQ h).inv.app
        (SheafOfModules.unit (XK).ringCatSheaf)).app U) s = _
  rw [Scheme.Modules.pushforwardComp_inv_app_app, Category.comp_id,
    Scheme.Modules.pushforwardCongr_hom_app_app]
  rfl

variable {ι κ : Type u} [Finite ι] [Finite κ]
  (b : Module.Basis ι K (Kernel q))
  (c : Module.Basis κ K
    (Kernel (ElementaryKernelSubspaceQuotient.reduction q W)))

/-- The matrix of the actual residue-kernel quotient in the two supplied finite bases. -/
def kernelQuotientMatrix : κ → ι → K :=
  coefficientMatrix b c (ElementaryKernelSubspaceQuotient.kernelLinearMap q W)

local instance : Fintype ι := Fintype.ofFinite ι

/-- Coordinates of the actual tensor quotient are its ordinary finite coefficient formula. -/
lemma residueTensorCoordinates_quotient
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens)
    (t : Γ(XK, iA ⁻¹ᵁ U) ⊗[K] Kernel q) (l : κ) :
    residueTensorCoordinates f r c ((h) ⁻¹ᵁ U)
        (quotientResidueTensorMap f q W U t) l =
      ∑ j, kernelQuotientMatrix q W b c l j •
        quotientResidueSectionMap f q W U (residueTensorCoordinates f q b U t j) :=
  tensorCoordinates_mapCoefficients b c
    (ElementaryKernelSubspaceQuotient.kernelLinearMap q W)
    (quotientResidueSectionMap f q W U) t l

/-- Each coordinate of the actual quotient sheaf map is the finite coefficient sum. -/
lemma quotientProductMap_coordinates
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens)
    (s : Γ(residueProductModule f (A := A) ι, U)) (l : κ) :
    residueProductSectionsEquiv f κ ((h) ⁻¹ᵁ U)
        ((quotientProductMap f q W b c).app U s) l =
      ∑ j, kernelQuotientMatrix q W b c l j •
        quotientResidueSectionMap f q W U (residueProductSectionsEquiv f ι U s j) := by
  calc
    _ = residueTensorCoordinates f r c ((h) ⁻¹ᵁ U)
        (productTensorEquiv f r c ((h) ⁻¹ᵁ U)
          ((quotientProductMap f q W b c).app U s)) l :=
      congrArg (fun z => z l)
        (residueTensorCoordinates_productTensorEquiv f r c ((h) ⁻¹ᵁ U) _).symm
    _ = _ := by
      rw [quotientProductMap_app, LinearEquiv.apply_symm_apply,
        residueTensorCoordinates_quotient f q W b c,
        residueTensorCoordinates_productTensorEquiv]

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianKernelQuotientCoordinates
