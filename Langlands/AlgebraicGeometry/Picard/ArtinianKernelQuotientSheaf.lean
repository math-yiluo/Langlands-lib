import Langlands.AlgebraicGeometry.Picard.ArtinianKernelQuotientResidue
import Langlands.AlgebraicGeometry.Picard.ArtinianResidueSheaf

/-! # Actual product-sheaf compatibility for an elementary kernel quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianKernelQuotientSheaf

open Langlands.AlgebraicGeometry.Deformation
open ArtinianTest ArtinianTest.ElementaryKernel
open ArtinianSquareZeroPicardLifting ArtinianPicardKernelTensor
open ArtinianPicardObstructionFinite ArtinianKernelQuotient
open ArtinianResidueSections ArtinianResidueKernel ArtinianResidueSheaf
open ArtinianKernelQuotientResidue
open Langlands.Scheme.Modules.BasisHomGluing

private lemma restriction_square {Y : Scheme.{u}} {U V S T : Y.Opens}
    (hVU : V ≤ U) (hSU : S ≤ U) (hTV : T ≤ V) (hTS : T ≤ S) (s : Γ(Y,U)) :
    Y.presheaf.map (homOfLE hTV).op (Y.presheaf.map (homOfLE hVU).op s) =
      Y.presheaf.map (homOfLE hTS).op (Y.presheaf.map (homOfLE hSU).op s) := by
  change (Y.presheaf.map (homOfLE hVU).op ≫
      Y.presheaf.map (homOfLE hTV).op) s =
    (Y.presheaf.map (homOfLE hSU).op ≫ Y.presheaf.map (homOfLE hTS).op) s
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

private lemma square_presentations {P Q S T I J : Type*}
    (a : S → I) (b : T → J) (u : I → J) (v : S → T)
    (e : P → S) (g : Q → T) (w : P → Q)
    (sq : ∀ s, u (a s) = b (v s)) (coord : ∀ p, g (w p) = v (e p))
    (p : P) : u (a (e p)) = b (g (w p)) :=
  (sq (e p)).trans (congrArg b (coord p).symm)

private lemma comp_pushforward_eq {Y Z : Scheme.{u}} (h : Z ⟶ Y)
    {M I : Y.Modules} {N J : Z.Modules}
    (a : M ⟶ I) (b : N ⟶ J)
    (v : I ⟶ (Scheme.Modules.pushforward h).obj J)
    (w : M ⟶ (Scheme.Modules.pushforward h).obj N)
    {P : Y.Opens → Prop}
    (basis : ∀ (y : Y) (U : Y.Opens), y ∈ U → ∃ V, P V ∧ y ∈ V ∧ V ≤ U)
    (sq : ∀ U, P U → ∀ s : Γ(M, U),
      v.app U (a.app U s) = b.app (h ⁻¹ᵁ U) (w.app U s)) :
    a ≫ v = w ≫ (Scheme.Modules.pushforward h).map b := by
  apply hom_ext_of_basis basis
  intro U hU
  ext s
  exact sq U hU s

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

attribute [local instance] sectionAlgebra residueSectionAlgebra residueSourceAlgebra

local instance : Fact (IsElementarySurjection r) :=
  ⟨ElementaryKernelSubspaceQuotient.reduction_elementary q W⟩
local instance : Module K (Kernel r) :=
  ElementaryKernel.residueModule r
    (ElementaryKernelSubspaceQuotient.reduction_elementary q W)

/-- The actual coefficient quotient retains the actual source-section scalar action. -/
lemma quotientResidueTensorMap_smul
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens)
    (a : Γ((relativeSpace f).obj (ArtinianTest.base A), U))
    (t : Γ(XK, iA ⁻¹ᵁ U) ⊗[K] Kernel q) :
    quotientResidueTensorMap f q W U (a • t) =
      (h).app U a • quotientResidueTensorMap f q W U t := by
  induction t using TensorProduct.inductionOn with
  | tmul s x =>
    change quotientResidueSectionMap f q W U ((iA).app U a * s) ⊗ₜ[K]
        ElementaryKernelSubspaceQuotient.kernelLinearMap q W x =
      ((iQ).app ((h) ⁻¹ᵁ U) ((h).app U a) *
        quotientResidueSectionMap f q W U s) ⊗ₜ[K]
          ElementaryKernelSubspaceQuotient.kernelLinearMap q W x
    rw [map_mul, quotientResidueSectionMap_app]
  | add x y hx hy =>
    simpa only [smul_add, LinearMap.map_add] using congrArg₂ (· + ·) hx hy

/-- The actual residue tensor quotient commutes with section restriction. -/
lemma quotientResidueTensorMap_res
    {U V : ((relativeSpace f).obj (ArtinianTest.base A)).Opens} (e : V ≤ U)
    (t : Γ(XK, iA ⁻¹ᵁ U) ⊗[K] Kernel q) :
    TensorProduct.map
        (residueSectionRestriction f
          (((Opens.map (iQ).base).map
            ((Opens.map (h).base).map (homOfLE e))).le)).toLinearMap LinearMap.id
          (quotientResidueTensorMap f q W U t) =
      quotientResidueTensorMap f q W V
        (TensorProduct.map
          (residueSectionRestriction f
            (((Opens.map (iA).base).map (homOfLE e)).le)).toLinearMap LinearMap.id t) := by
  induction t using TensorProduct.inductionOn with
  | tmul s x =>
    change
      (XK).presheaf.map _ ((XK).presheaf.map _ s) ⊗ₜ[K]
          ElementaryKernelSubspaceQuotient.kernelLinearMap q W x =
        (XK).presheaf.map _ ((XK).presheaf.map _ s) ⊗ₜ[K]
          ElementaryKernelSubspaceQuotient.kernelLinearMap q W x
    exact congrArg (fun z => z ⊗ₜ[K]
      ElementaryKernelSubspaceQuotient.kernelLinearMap q W x)
        (restriction_square _ _ _ _ s)
  | add x y hx hy =>
    simpa only [LinearMap.map_add] using congrArg₂ (· + ·) hx hy

variable {ι κ : Type u} [Finite ι] [Finite κ]
  (b : Module.Basis ι K (Kernel q))
variable (c : Module.Basis κ K
  (Kernel (ElementaryKernelSubspaceQuotient.reduction q W)))

/-- The underlying additive map on product sections. -/
def quotientProductSectionsAddHom
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) :
    Γ(residueProductModule f (A := A) ι, U) →+
      Γ(residueProductModule f (A := AQ) κ, (h) ⁻¹ᵁ U) :=
  (productTensorEquiv (A := AQ) (B := B) f r c ((h) ⁻¹ᵁ U)).symm.toAddMonoidHom.comp
    ((quotientResidueTensorMap f q W U).toAddMonoidHom.comp
      (productTensorEquiv f q b U).toAddMonoidHom)

/-- The actual quotient on tensor coefficients, presented in finite product sections. -/
def quotientProductSections
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) :
    Γ(residueProductModule f (A := A) ι, U) →ₗ[Γ((relativeSpace f).obj (ArtinianTest.base A), U)]
      Γ((Scheme.Modules.pushforward h).obj (residueProductModule f (A := AQ) κ), U) where
  toFun := quotientProductSectionsAddHom f q W b c U
  map_add' := (quotientProductSectionsAddHom f q W b c U).map_add
  map_smul' a s := by
    change (productTensorEquiv (A := AQ) (B := B) f r c ((h) ⁻¹ᵁ U)).symm
        (quotientResidueTensorMap f q W U (productTensorEquiv f q b U (a • s))) =
      (h).app U a • (productTensorEquiv (A := AQ) (B := B) f r c ((h) ⁻¹ᵁ U)).symm
        (quotientResidueTensorMap f q W U (productTensorEquiv f q b U s))
    rw [LinearEquiv.map_smul, quotientResidueTensorMap_smul, LinearEquiv.map_smul]

set_option maxRecDepth 2048 in
/-- The finite product presentation commutes with the actual presheaf restrictions. -/
lemma quotientProductSections_res
    {U V : ((relativeSpace f).obj (ArtinianTest.base A)).Opens} (e : V ≤ U)
    (s : Γ(residueProductModule f (A := A) ι, U)) :
    ((Scheme.Modules.pushforward h).obj
        (residueProductModule f (A := AQ) κ)).presheaf.map (homOfLE e).op
          (quotientProductSections f q W b c U s) =
      quotientProductSections f q W b c V
        ((residueProductModule f (A := A) ι).presheaf.map (homOfLE e).op s) := by
  apply (productTensorEquiv (A := AQ) (B := B) f r c ((h) ⁻¹ᵁ V)).injective
  change productTensorEquiv (A := AQ) (B := B) f r c ((h) ⁻¹ᵁ V)
      ((residueProductModule f (A := AQ) κ).presheaf.map
        (homOfLE (((Opens.map (h).base).map (homOfLE e)).le)).op
          ((productTensorEquiv (A := AQ) (B := B) f r c ((h) ⁻¹ᵁ U)).symm
            (quotientResidueTensorMap f q W U (productTensorEquiv f q b U s)))) =
    productTensorEquiv (A := AQ) (B := B) f r c ((h) ⁻¹ᵁ V)
      ((productTensorEquiv (A := AQ) (B := B) f r c ((h) ⁻¹ᵁ V)).symm
        (quotientResidueTensorMap f q W V (productTensorEquiv f q b V
          ((residueProductModule f (A := A) ι).presheaf.map (homOfLE e).op s))))
  rw [← productTensorEquiv_res f r c
      (((Opens.map (h).base).map (homOfLE e)).le),
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    quotientResidueTensorMap_res f q W e, productTensorEquiv_res f q b e]

/-- A sheaf map constructed from actual residue restriction and the actual kernel quotient. -/
def quotientProductMap :
    residueProductModule f (A := A) ι ⟶
      (Scheme.Modules.pushforward h).obj (residueProductModule f (A := AQ) κ) where
  val := PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        (quotientProductSections f q W b c U.unop).toAddMonoidHom
      naturality := by
        intro U V e
        ext s
        exact (quotientProductSections_res f q W b c (leOfHom e.unop) s).symm }
    (by intro U a s; exact (quotientProductSections f q W b c U.unop).map_smul a s)

set_option maxRecDepth 2048 in
lemma quotientProductMap_app
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens)
    (s : Γ(residueProductModule f (A := A) ι, U)) :
    (quotientProductMap f q W b c).app U s =
      (productTensorEquiv (A := AQ) (B := B) f r c ((h) ⁻¹ᵁ U)).symm
        (quotientResidueTensorMap f q W U (productTensorEquiv f q b U s)) := rfl

set_option maxRecDepth 2048 in
lemma productTensorEquiv_quotientProductSections
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens)
    (s : Γ(residueProductModule f (A := A) ι, U)) :
    productTensorEquiv (A := AQ) (B := B) f r c ((h) ⁻¹ᵁ U)
        (quotientProductSections f q W b c U s) =
      quotientResidueTensorMap f q W U (productTensorEquiv f q b U s) :=
  (productTensorEquiv (A := AQ) (B := B) f r c ((h) ⁻¹ᵁ U)).apply_symm_apply _

private lemma residueValue_quotient [Flat f]
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen ((h) ⁻¹ᵁ U)) (t : Γ(XK, iA ⁻¹ᵁ U) ⊗[K] Kernel q) :
    (h).app U (affineKernelResidueEquiv f q U hU t).val =
      (affineKernelResidueEquiv f r ((h) ⁻¹ᵁ U) hV
        (quotientResidueTensorMap f q W U t)).val := by
  calc
    _ = ((idealMap f q W).app U (affineKernelResidueEquiv f q U hU t)).val :=
      (idealMap_app f q W U _).symm
    _ = _ := congrArg (fun z : Γ(idealModule f r, (h) ⁻¹ᵁ U) => z.val)
      (affineKernelResidueEquiv_quotient f q W U hU hV t)

set_option maxRecDepth 2048 in
private lemma productValue_quotient [Flat f]
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen ((h) ⁻¹ᵁ U))
    (s : Γ(residueProductModule f (A := A) ι, U)) :
    (h).app U (affineProductIdealEquiv f q b U hU s).val =
      (affineProductIdealEquiv f r c ((h) ⁻¹ᵁ U) hV
        (quotientProductSections f q W b c U s)).val := by
  exact square_presentations
    (fun t => (affineKernelResidueEquiv f q U hU t).val)
    (fun t => (affineKernelResidueEquiv f r ((h) ⁻¹ᵁ U) hV t).val)
    ((h).app U) (quotientResidueTensorMap f q W U)
    (productTensorEquiv f q b U)
    (productTensorEquiv (A := AQ) (B := B) f r c ((h) ⁻¹ᵁ U))
    (quotientProductSections f q W b c U)
    (residueValue_quotient f q W U hU hV)
    (productTensorEquiv_quotientProductSections f q W b c U) s

set_option maxRecDepth 2048 in
/-- The affine ideal equivalences commute with the coefficient quotient. -/
lemma affineProductIdealEquiv_quotient [Flat f]
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen ((h) ⁻¹ᵁ U))
    (s : Γ(residueProductModule f (A := A) ι, U)) :
    (idealMap f q W).app U (affineProductIdealEquiv f q b U hU s) =
      affineProductIdealEquiv f r c ((h) ⁻¹ᵁ U) hV
        (quotientProductSections f q W b c U s) := by
  apply Subtype.ext
  calc
    _ = (h).app U (affineProductIdealEquiv f q b U hU s).val :=
      idealMap_app f q W U _
    _ = _ := productValue_quotient f q W b c U hU hV s

set_option maxRecDepth 2048 in
/-- The independently constructed ideal quotient agrees with the actual coefficient sheaf map. -/
lemma productToIdeal_quotient [Flat f] :
    productToIdeal f q b ≫ idealMap f q W =
      quotientProductMap f q W b c ≫
        (Scheme.Modules.pushforward h).map (productToIdeal f r c) := by
  let : IsClosedImmersion h :=
    relativeMap_isClosedImmersion f π
      (ElementaryKernelSubspaceQuotient.projection_elementary q W).1
  apply comp_pushforward_eq h (productToIdeal f q b) (productToIdeal f r c)
    (idealMap f q W) (quotientProductMap f q W b c)
    (P := IsAffineOpen) (fun _ _ hy => exists_isAffineOpen_mem_and_subset hy)
  intro U hU s
  have hV : IsAffineOpen ((h) ⁻¹ᵁ U) := hU.preimage h
  rw [productToIdeal_app f q b U hU,
    productToIdeal_app f r c ((h) ⁻¹ᵁ U) hV]
  exact affineProductIdealEquiv_quotient f q W b c U hU hV s

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianKernelQuotientSheaf
