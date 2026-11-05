import Langlands.AlgebraicGeometry.Picard.ArtinianKernelQuotientTensor
import Langlands.AlgebraicGeometry.Picard.ArtinianResidueKernel

/-! # Actual residue-coordinate compatibility for an elementary kernel quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianKernelQuotientResidue

open Langlands.AlgebraicGeometry.Deformation
open ArtinianTest ArtinianTest.ElementaryKernel
open ArtinianSquareZeroPicardLifting ArtinianPicardKernelTensor
open ArtinianPicardObstructionFinite ArtinianKernelQuotient
open ArtinianKernelQuotientTensor ArtinianResidueSections ArtinianResidueKernel

private lemma factorization_preimage {T Y Z : Scheme.{u}}
    (j : Z ⟶ Y) (h : Y ⟶ T) {i : Z ⟶ T} (w : j ≫ h = i) (U : T.Opens) :
    j ⁻¹ᵁ (h ⁻¹ᵁ U) = i ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, w]

private lemma factorization_section {T Y Z : Scheme.{u}}
    (j : Z ⟶ Y) (h : Y ⟶ T) {i : Z ⟶ T} (w : j ≫ h = i) (U : T.Opens)
    (s : Γ(T, U)) :
    Z.presheaf.map (homOfLE (le_of_eq (factorization_preimage j h w U))).op
        (i.app U s) = j.app (h ⁻¹ᵁ U) (h.app U s) := by
  cases w
  change Z.presheaf.map (𝟙 (Opposite.op (j ⁻¹ᵁ (h ⁻¹ᵁ U)))) ((j ≫ h).app U s) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

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

local instance (C : ArtinianTest k K) : Algebra C.algebra K :=
  C.augmentation.toRingHom.toAlgebra

local instance : Fact (IsElementarySurjection r) :=
  ⟨ElementaryKernelSubspaceQuotient.reduction_elementary q W⟩

local instance : Module K (Kernel r) :=
  ElementaryKernel.residueModule r
    (ElementaryKernelSubspaceQuotient.reduction_elementary q W)

/-- The actual residue immersion factors through the actual quotient. -/
lemma residue_factorization : iQ ≫ h = iA := by
  rw [← Functor.map_comp, ArtinianTest.reduction_baseMap]

/-- Both actual residue inverse-image opens coincide. -/
lemma residue_open_eq
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) :
    iQ ⁻¹ᵁ ((h) ⁻¹ᵁ U) = iA ⁻¹ᵁ U :=
  factorization_preimage iQ h (residue_factorization f q W) U

/-- The actual restriction between the equal residue opens. -/
def quotientResidueSectionMap
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) :
    Γ(XK, iA ⁻¹ᵁ U) →ₐ[K] Γ(XK, iQ ⁻¹ᵁ ((h) ⁻¹ᵁ U)) :=
  residueSectionRestriction f (le_of_eq (residue_open_eq f q W U))

/-- Actual restriction preserves the specified residue scalars. -/
lemma quotientResidueSectionMap_scalar
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (c : K) :
    quotientResidueSectionMap f q W U (residueSectionHom f (iA ⁻¹ᵁ U) c) =
      residueSectionHom f (iQ ⁻¹ᵁ ((h) ⁻¹ᵁ U)) c :=
  (quotientResidueSectionMap f q W U).commutes c

/-- Restriction identifies the actual composite section maps. -/
lemma quotientResidueSectionMap_app
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens)
    (s : Γ((relativeSpace f).obj (ArtinianTest.base A), U)) :
    quotientResidueSectionMap f q W U ((iA).app U s) =
      (iQ).app ((h) ⁻¹ᵁ U) ((h).app U s) :=
  factorization_section iQ h (residue_factorization f q W) U s

/-- The affine residue-section comparison intertwines the actual quotient maps. -/
lemma affineSectionsEquiv_quotient
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen ((h) ⁻¹ᵁ U)) (y : FibreSections f A U) :
    quotientResidueSectionMap f q W U (affineSectionsEquiv f A U hU y) =
      affineSectionsEquiv f AQ ((h) ⁻¹ᵁ U) hV (quotientFibreMap f q W U y) := by
  induction y using TensorProduct.inductionOn with
  | tmul c s =>
    rw [affineSectionsEquiv_tmul, map_mul, quotientResidueSectionMap_scalar,
      quotientResidueSectionMap_app, quotientFibreMap_tmul, affineSectionsEquiv_tmul]
  | add a b ha hb =>
    simpa only [map_add] using congrArg₂ (· + ·) ha hb

/-- Actual residue restriction tensored with the actual residue-kernel quotient. -/
def quotientResidueTensorMap
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) :
    Γ(XK, iA ⁻¹ᵁ U) ⊗[K] Kernel q →ₗ[K]
      Γ(XK, iQ ⁻¹ᵁ ((h) ⁻¹ᵁ U)) ⊗[K] Kernel r :=
  TensorProduct.map (quotientResidueSectionMap f q W U).toLinearMap
    (ElementaryKernelSubspaceQuotient.kernelLinearMap q W)

/-- Actual coefficient-section comparisons commute with the quotient tensors. -/
lemma coefficientSectionsEquiv_quotient
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen ((h) ⁻¹ᵁ U)) (t : FibreSections f A U ⊗[K] Kernel q) :
    quotientResidueTensorMap f q W U (coefficientSectionsEquiv f q U hU t) =
      coefficientSectionsEquiv f r ((h) ⁻¹ᵁ U) hV (quotientTensorMap f q W U t) := by
  induction t using TensorProduct.inductionOn with
  | tmul y x =>
    simp only [coefficientSectionsEquiv_tmul, quotientResidueTensorMap,
      quotientTensorMap, TensorProduct.map_tmul, AlgHom.toLinearMap_apply]
    rw [affineSectionsEquiv_quotient f q W U hU hV]
  | add a b ha hb =>
    simpa only [LinearEquiv.map_add, LinearMap.map_add]
      using congrArg₂ (· + ·) ha hb

private lemma transfer_square {P Q P' Q' J J' : Type u}
    (e : P ≃ Q) (e' : P' ≃ Q') (a : P → J) (a' : P' → J')
    (g : J → J') (m : P → P') (n : Q → Q')
    (w : ∀ s, n (e s) = e' (m s)) (v : ∀ s, g (a s) = a' (m s)) (t : Q) :
    g (a (e.symm t)) = a' (e'.symm (n t)) := by
  obtain ⟨s, rfl⟩ := e.surjective t
  rw [e.symm_apply_apply, w, e'.symm_apply_apply, v]

variable [Flat f]

private lemma affine_value_quotient
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen ((h) ⁻¹ᵁ U)) (t : FibreSections f A U ⊗[K] Kernel q) :
    (h).app U (affineKernelEquiv f q U hU t).val =
      (affineKernelEquiv f r ((h) ⁻¹ᵁ U) hV (quotientTensorMap f q W U t)).val := by
  calc
    _ = ((idealMap f q W).app U (affineKernelEquiv f q U hU t)).val :=
      (idealMap_app f q W U _).symm
    _ = _ := congrArg (fun z : Γ(idealModule f r, (h) ⁻¹ᵁ U) => z.val)
      (affineKernelEquiv_quotient f q W U hU hV t)

private lemma residue_value_quotient
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen ((h) ⁻¹ᵁ U)) (t : Γ(XK, iA ⁻¹ᵁ U) ⊗[K] Kernel q) :
    (h).app U (affineKernelResidueEquiv f q U hU t).val =
      (affineKernelResidueEquiv f r ((h) ⁻¹ᵁ U) hV
        (quotientResidueTensorMap f q W U t)).val := by
  exact transfer_square (coefficientSectionsEquiv f q U hU).toEquiv
    (coefficientSectionsEquiv f r ((h) ⁻¹ᵁ U) hV).toEquiv
    (fun s => (affineKernelEquiv f q U hU s).val)
    (fun s => (affineKernelEquiv f r ((h) ⁻¹ᵁ U) hV s).val)
    ((h).app U) (quotientTensorMap f q W U)
    (quotientResidueTensorMap f q W U)
    (coefficientSectionsEquiv_quotient f q W U hU hV)
    (affine_value_quotient f q W U hU hV) t

/-- The actual ideal quotient map is the actual residue-coefficient tensor map. -/
lemma affineKernelResidueEquiv_quotient
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen ((h) ⁻¹ᵁ U)) (t : Γ(XK, iA ⁻¹ᵁ U) ⊗[K] Kernel q) :
    (idealMap f q W).app U (affineKernelResidueEquiv f q U hU t) =
      affineKernelResidueEquiv f r ((h) ⁻¹ᵁ U) hV (quotientResidueTensorMap f q W U t) := by
  apply Subtype.ext
  calc
    _ = (h).app U (affineKernelResidueEquiv f q U hU t).val :=
      idealMap_app f q W U _
    _ = _ := residue_value_quotient f q W U hU hV t

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianKernelQuotientResidue
