import Langlands.AlgebraicGeometry.Picard.ArtinianResidueKernel
import Langlands.AlgebraicGeometry.Modules.BasisHomGluing
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Finite residue coefficients as the actual elementary ideal sheaf -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianResidueSheaf

open Langlands.AlgebraicGeometry.Deformation
open ArtinianTest ArtinianTest.ElementaryKernel
open ArtinianSquareZeroPicardLifting ArtinianPicardKernelTensor
open ArtinianResidueSections ArtinianResidueKernel ArtinianPicardObstructionFinite
open Langlands.Scheme.Modules.BasisHomGluing
open Langlands.Scheme.Modules.OpenCoverHomGluing

section Products

variable {Y : Scheme.{u}} (M : Y.Modules) (ι : Type u)

/-- Sections of a product of actual modules are the actual product of sections. -/
def productSectionsIso (U : Y.Opens) :
    (SheafOfModules.evaluation Y.ringCatSheaf (op U)).obj
        (∏ᶜ fun _ : ι => M) ≅
      ModuleCat.of Γ(Y, U) (ι → Γ(M, U)) :=
  PreservesProduct.iso (SheafOfModules.evaluation Y.ringCatSheaf (op U))
      (fun _ : ι => M) ≪≫ ModuleCat.piIsoPi _

lemma productSectionsIso_apply (U : Y.Opens)
    (s : Γ(∏ᶜ fun _ : ι => M, U)) (j : ι) :
    (productSectionsIso M ι U).hom s j = (Pi.π (fun _ : ι => M) j).app U s := by
  have h := congrArg (fun a => a
    ((PreservesProduct.iso (SheafOfModules.evaluation Y.ringCatSheaf (op U))
      (fun _ : ι => M)).hom s))
    ((ModuleCat.piIsoPi_hom_ker_subtype
      (fun _ : ι => (SheafOfModules.evaluation Y.ringCatSheaf (op U)).obj M) j))
  change (productSectionsIso M ι U).hom s j = _
  simp only [productSectionsIso, Iso.trans_hom, ConcreteCategory.comp_apply] at ⊢
  rw [← ConcreteCategory.comp_apply]
  have hh := piComparison_comp_π
    (SheafOfModules.evaluation Y.ringCatSheaf (op U)) (fun _ : ι => M) j
  exact h.trans (congrArg (fun a => a s) hh)

lemma productSectionsIso_res {U V : Y.Opens} (h : V ≤ U)
    (s : Γ(∏ᶜ fun _ : ι => M, U)) (j : ι) :
    (productSectionsIso M ι V).hom
        ((∏ᶜ fun _ : ι => M).presheaf.map (homOfLE h).op s) j =
      M.presheaf.map (homOfLE h).op ((productSectionsIso M ι U).hom s j) := by
  rw [productSectionsIso_apply, productSectionsIso_apply]
  exact (hom_map_app (Pi.π (fun _ : ι => M) j) h s).symm

end Products

section Coordinates

variable {K V ι : Type u} [Field K] [AddCommGroup V] [Module K V]
  [Finite ι] (b : Module.Basis ι K V)
  (S : Type u) [CommRing S] [Algebra K S]

/-- Tensor coordinates for a chosen finite basis of the coefficient space. -/
def tensorCoordinates : S ⊗[K] V ≃ₗ[S] (ι → S) :=
  (b.baseChange S).equivFun

@[simp]
lemma tensorCoordinates_tmul (s : S) (v : V) (j : ι) :
    tensorCoordinates b S (s ⊗ₜ[K] v) j = b.repr v j • s := by
  exact Module.Basis.baseChange_repr_tmul S b s v j

/-- Tensor coordinates commute with a change of the section algebra. -/
lemma tensorCoordinates_map {T : Type u} [CommRing T] [Algebra K T]
    (φ : S →ₐ[K] T) (t : S ⊗[K] V) (j : ι) :
    tensorCoordinates b T (TensorProduct.map φ.toLinearMap LinearMap.id t) j =
      φ (tensorCoordinates b S t j) := by
  induction t using TensorProduct.inductionOn with
  | tmul s v =>
    simpa only [TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply,
      tensorCoordinates_tmul] using (φ.toLinearMap.map_smul (b.repr v j) s).symm
  | add x y hx hy =>
    simpa only [LinearMap.map_add, LinearEquiv.map_add, Pi.add_apply, map_add]
      using congrArg₂ (· + ·) hx hy

end Coordinates

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  {A B : ArtinianTest k K} (q : A ⟶ B)
  [he : Fact (IsElementarySurjection q)]

local notation "hq" => he.out
local notation "i" => residueMap f A

attribute [local instance] sectionAlgebra residueSectionAlgebra residueSourceAlgebra

local instance : Module K (Kernel q) := ElementaryKernel.residueModule q hq

/-- The actual residue-fibre structure module pushed to the source test scheme. -/
abbrev residueStructureModule :
    ((relativeSpace f).obj (ArtinianTest.base A)).Modules :=
  (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit
      ((relativeSpace f).obj (ArtinianTest.residueBase k K)).ringCatSheaf)

/-- A finite product of the actual residue-fibre structure module, pushed to `X_A`. -/
def residueProductModule (ι : Type u) :
    ((relativeSpace f).obj (ArtinianTest.base A)).Modules :=
  ∏ᶜ fun _ : ι => residueStructureModule f (A := A)

/-- Actual product-sheaf sections are tuples of actual residue sections. -/
def residueProductSectionsEquiv (ι : Type u)
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) :
    Γ(residueProductModule f (A := A) ι, U)
      ≃ₗ[Γ((relativeSpace f).obj (ArtinianTest.base A), U)]
        (ι → Γ((relativeSpace f).obj (ArtinianTest.residueBase k K), i ⁻¹ᵁ U)) :=
  (productSectionsIso (residueStructureModule f (A := A)) ι U).toLinearEquiv

lemma residueProductSectionsEquiv_res (ι : Type u)
    {U V : ((relativeSpace f).obj (ArtinianTest.base A)).Opens} (h : V ≤ U)
    (s : Γ(residueProductModule f (A := A) ι, U)) (j : ι) :
    residueProductSectionsEquiv f ι V
        ((residueProductModule f (A := A) ι).presheaf.map (homOfLE h).op s) j =
      residueSectionRestriction f
        (((Opens.map (i).base).map (homOfLE h)).le)
          (residueProductSectionsEquiv f ι U s j) :=
  productSectionsIso_res (residueStructureModule f (A := A)) ι h s j

variable {ι : Type u} [Finite ι] (b : Module.Basis ι K (Kernel q))

/-- Tensor coordinates, retaining the actual source-section scalar action. -/
def residueTensorCoordinates
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) :
    Γ((relativeSpace f).obj (ArtinianTest.residueBase k K), i ⁻¹ᵁ U) ⊗[K] Kernel q
      ≃ₗ[Γ((relativeSpace f).obj (ArtinianTest.base A), U)]
        (ι → Γ((relativeSpace f).obj (ArtinianTest.residueBase k K), i ⁻¹ᵁ U)) :=
  (tensorCoordinates b
    Γ((relativeSpace f).obj (ArtinianTest.residueBase k K), i ⁻¹ᵁ U)).restrictScalars _

/-- The product sheaf presents the actual tensor coefficients on every open. -/
def productTensorEquiv
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) :
    Γ(residueProductModule f (A := A) ι, U)
      ≃ₗ[Γ((relativeSpace f).obj (ArtinianTest.base A), U)]
        Γ((relativeSpace f).obj (ArtinianTest.residueBase k K), i ⁻¹ᵁ U) ⊗[K] Kernel q :=
  (residueProductSectionsEquiv f ι U).trans (residueTensorCoordinates f q b U).symm

@[simp]
lemma residueTensorCoordinates_productTensorEquiv
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens)
    (s : Γ(residueProductModule f (A := A) ι, U)) :
    residueTensorCoordinates f q b U (productTensorEquiv f q b U s) =
      residueProductSectionsEquiv f ι U s :=
  (residueTensorCoordinates f q b U).apply_symm_apply _

lemma residueTensorCoordinates_res
    {U V : ((relativeSpace f).obj (ArtinianTest.base A)).Opens} (h : V ≤ U)
    (t : Γ((relativeSpace f).obj (ArtinianTest.residueBase k K), i ⁻¹ᵁ U) ⊗[K] Kernel q)
    (j : ι) :
    residueTensorCoordinates f q b V
        (TensorProduct.map
          (residueSectionRestriction f
            (((Opens.map (i).base).map (homOfLE h)).le)).toLinearMap LinearMap.id t) j =
      residueSectionRestriction f
        (((Opens.map (i).base).map (homOfLE h)).le)
          (residueTensorCoordinates f q b U t j) :=
  tensorCoordinates_map b _
    (residueSectionRestriction f (((Opens.map (i).base).map (homOfLE h)).le)) t j

/-- The tensor presentation respects the actual restriction maps. -/
lemma productTensorEquiv_res
    {U V : ((relativeSpace f).obj (ArtinianTest.base A)).Opens} (h : V ≤ U)
    (s : Γ(residueProductModule f (A := A) ι, U)) :
    TensorProduct.map
        (residueSectionRestriction f
          (((Opens.map (i).base).map (homOfLE h)).le)).toLinearMap LinearMap.id
          (productTensorEquiv f q b U s) =
      productTensorEquiv f q b V
        ((residueProductModule f (A := A) ι).presheaf.map (homOfLE h).op s) := by
  apply (residueTensorCoordinates f q b V).injective
  ext j
  rw [residueTensorCoordinates_res f q b h, residueTensorCoordinates_productTensorEquiv,
    residueTensorCoordinates_productTensorEquiv]
  exact (residueProductSectionsEquiv_res f ι h s j).symm

variable [Flat f]

/-- On an affine open the residue product is the actual elementary ideal module. -/
def affineProductIdealEquiv
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U) :
    Γ(residueProductModule f (A := A) ι, U)
      ≃ₗ[Γ((relativeSpace f).obj (ArtinianTest.base A), U)] Γ(idealModule f q, U) :=
  (productTensorEquiv f q b U).trans (affineKernelResidueEquiv f q U hU)

lemma affineProductIdealEquiv_res
    {U V : ((relativeSpace f).obj (ArtinianTest.base A)).Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (s : Γ(residueProductModule f (A := A) ι, U)) :
    (idealModule f q).presheaf.map (homOfLE h).op
        (affineProductIdealEquiv f q b U hU s) =
      affineProductIdealEquiv f q b V hV
        ((residueProductModule f (A := A) ι).presheaf.map (homOfLE h).op s) := by
  simp only [affineProductIdealEquiv, LinearEquiv.trans_apply]
  rw [affineKernelResidueEquiv_res, productTensorEquiv_res]

lemma affineProductIdealEquiv_symm_res
    {U V : ((relativeSpace f).obj (ArtinianTest.base A)).Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (s : Γ(idealModule f q, U)) :
    (residueProductModule f (A := A) ι).presheaf.map (homOfLE h).op
        ((affineProductIdealEquiv f q b U hU).symm s) =
      (affineProductIdealEquiv f q b V hV).symm
        ((idealModule f q).presheaf.map (homOfLE h).op s) := by
  apply (affineProductIdealEquiv f q b V hV).injective
  rw [← affineProductIdealEquiv_res f q b h hU hV, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

omit [Flat f] in
private lemma affineBasis
    (y : (relativeSpace f).obj (ArtinianTest.base A))
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hy : y ∈ U) :
    ∃ V, IsAffineOpen V ∧ y ∈ V ∧ V ≤ U :=
  exists_isAffineOpen_mem_and_subset hy

/-- Glue the affine coefficient maps into a morphism of actual module sheaves. -/
def productToIdeal : residueProductModule f (A := A) ι ⟶ idealModule f q :=
  Langlands.Scheme.Modules.BasisHomGluing.hom (affineBasis f)
    (fun U hU => (affineProductIdealEquiv f q b U hU).toLinearMap)
    (fun _ _ hU hV h s => affineProductIdealEquiv_res f q b h hU hV s)

/-- Glue the inverse affine coefficient maps. -/
def idealToProduct : idealModule f q ⟶ residueProductModule f (A := A) ι :=
  Langlands.Scheme.Modules.BasisHomGluing.hom (affineBasis f)
    (fun U hU => (affineProductIdealEquiv f q b U hU).symm.toLinearMap)
    (fun _ _ hU hV h s => affineProductIdealEquiv_symm_res f q b h hU hV s)

lemma productToIdeal_app
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (s : Γ(residueProductModule f (A := A) ι, U)) :
    (productToIdeal f q b).app U s = affineProductIdealEquiv f q b U hU s :=
  hom_app_basis (affineBasis f) _ _ U hU s

lemma idealToProduct_app
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (s : Γ(idealModule f q, U)) :
    (idealToProduct f q b).app U s = (affineProductIdealEquiv f q b U hU).symm s :=
  hom_app_basis (affineBasis f) _ _ U hU s

/-- A chosen finite kernel basis identifies the actual ideal sheaf with residue products. -/
def residueProductIdealIso : residueProductModule f (A := A) ι ≅ idealModule f q where
  hom := productToIdeal f q b
  inv := idealToProduct f q b
  hom_inv_id := by
    apply hom_ext_of_basis (affineBasis f)
    intro U hU
    ext s
    change (idealToProduct f q b).app U ((productToIdeal f q b).app U s) = s
    rw [productToIdeal_app f q b U hU, idealToProduct_app f q b U hU]
    exact (affineProductIdealEquiv f q b U hU).symm_apply_apply s
  inv_hom_id := by
    apply hom_ext_of_basis (affineBasis f)
    intro U hU
    ext s
    change (productToIdeal f q b).app U ((idealToProduct f q b).app U s) = s
    rw [idealToProduct_app f q b U hU, productToIdeal_app f q b U hU]
    exact (affineProductIdealEquiv f q b U hU).apply_symm_apply s

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianResidueSheaf
