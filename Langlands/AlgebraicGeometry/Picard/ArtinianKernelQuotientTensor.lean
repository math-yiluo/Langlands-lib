import Langlands.AlgebraicGeometry.Picard.ArtinianKernelQuotient
import Langlands.AlgebraicGeometry.Picard.ArtinianPicardKernelTensor

/-! # Actual affine tensor comparison for an elementary kernel quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianKernelQuotientTensor

open Langlands.AlgebraicGeometry.Deformation
open ArtinianTest ArtinianTest.ElementaryKernel
open ArtinianSquareZeroPicardLifting ArtinianPicardKernelTensor
open ArtinianPicardObstructionFinite ArtinianKernelQuotient

private lemma appLE_congr {T Y : Scheme.{u}} {p p' : Y ⟶ T}
    (w : p = p') (U : T.Opens) (V : Y.Opens) (e : V ≤ p ⁻¹ᵁ U) :
    p.appLE U V e = p'.appLE U V (w ▸ e) := by
  cases w
  rfl

lemma baseScalar_naturality {T Y : Scheme.{u}} {R S : CommRingCat.{u}}
    (h : Y ⟶ T) (p : T ⟶ Spec R) (p' : Y ⟶ Spec S) (φ : R ⟶ S)
    (w : h ≫ p = p' ≫ Spec.map φ) (U : T.Opens) (a : R) :
    h.app U (p.appLE ⊤ U le_top ((Scheme.ΓSpecIso R).inv a)) =
      p'.appLE ⊤ (h ⁻¹ᵁ U) le_top ((Scheme.ΓSpecIso S).inv (φ a)) := by
  have hh : p.appLE ⊤ U le_top ≫ h.appLE U (h ⁻¹ᵁ U) le_rfl =
      (Spec.map φ).appTop ≫ p'.appLE ⊤ (h ⁻¹ᵁ U) le_top := by
    rw [Scheme.Hom.appLE_comp_appLE, appLE_congr w, Scheme.Hom.comp_appLE]
    rfl
  have ht : (Scheme.ΓSpecIso R).inv ≫ p.appLE ⊤ U le_top ≫ h.app U =
      φ ≫ (Scheme.ΓSpecIso S).inv ≫ p'.appLE ⊤ (h ⁻¹ᵁ U) le_top := by
    rw [Scheme.Hom.app_eq_appLE, hh, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  exact ConcreteCategory.congr_hom ht a

private lemma nestedTensor_addHom_ext
    {R F S M N : Type u} [CommRing R] [CommRing F] [Algebra R F]
    [AddCommGroup S] [Module R S] [AddCommGroup M] [Module F M]
    [AddCommGroup N]
    (a b : ((F ⊗[R] S) ⊗[F] M) →+ N)
    (w : ∀ c s x, a ((c ⊗ₜ[R] s) ⊗ₜ[F] x) = b ((c ⊗ₜ[R] s) ⊗ₜ[F] x)) :
    a = b := by
  apply AddMonoidHom.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul y x =>
    induction y using TensorProduct.inductionOn with
    | tmul c s => exact w c s x
    | add a' b' ha hb =>
      simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) ha hb
  | add a' b' ha hb =>
    simpa only [map_add] using congrArg₂ (· + ·) ha hb

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
local notation "φ" => AlgHom.toRingHom (ArtinianTest.toAlgHom π)

/-- The quotient structure map carries actual source scalars to actual quotient scalars. -/
lemma quotient_testSectionHom
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (a : A.algebra) :
    (h).app U (testSectionHom f A U a) =
      testSectionHom f AQ ((h) ⁻¹ᵁ U) (φ a) :=
  baseScalar_naturality h pA pQ (CommRingCat.ofHom φ) (projection_square f q W) U a

attribute [local instance] sectionAlgebra

local instance (C : ArtinianTest k K) : Algebra C.algebra K :=
  C.augmentation.toRingHom.toAlgebra

local instance : Fact (IsElementarySurjection r) :=
  ⟨ElementaryKernelSubspaceQuotient.reduction_elementary q W⟩

local instance : Module K (Kernel r) :=
  ElementaryKernel.residueModule r
    (ElementaryKernelSubspaceQuotient.reduction_elementary q W)

/-- The algebraic residue-fibre sections, using the specified augmentation. -/
abbrev FibreSections (C : ArtinianTest k K)
    (U : ((relativeSpace f).obj (ArtinianTest.base C)).Opens) :=
  K ⊗[C.algebra] Γ((relativeSpace f).obj (ArtinianTest.base C), U)

local instance (C : ArtinianTest k K)
    (U : ((relativeSpace f).obj (ArtinianTest.base C)).Opens) :
    Algebra Γ((relativeSpace f).obj (ArtinianTest.base C), U) (FibreSections f C U) :=
  Algebra.TensorProduct.rightAlgebra

/-- The fibre-section ring map induced by the actual quotient structure map. -/
def quotientFibreRingHom
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) :
    FibreSections f A U →+* FibreSections f AQ ((h) ⁻¹ᵁ U) :=
  Algebra.TensorProduct.mapRingHom φ (RingHom.id K) ((h).app U).hom rfl (by
    ext a
    exact quotient_testSectionHom f q W U a)

@[simp]
lemma quotientFibreRingHom_tmul
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens)
    (c : K) (s : Γ((relativeSpace f).obj (ArtinianTest.base A), U)) :
    quotientFibreRingHom f q W U (c ⊗ₜ[A.algebra] s) =
      c ⊗ₜ[(AQ).algebra] (h).app U s :=
  Algebra.TensorProduct.mapRingHom_tmul _ _ _ _ _ c s

/-- The actual quotient fibre-section map is linear over the unchanged residue field. -/
def quotientFibreMap
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) :
    FibreSections f A U →ₐ[K] FibreSections f AQ ((h) ⁻¹ᵁ U) :=
  { quotientFibreRingHom f q W U with
    commutes' := by
      intro c
      change quotientFibreRingHom f q W U (c ⊗ₜ[A.algebra] 1) =
        c ⊗ₜ[(AQ).algebra] 1
      rw [quotientFibreRingHom_tmul, map_one] }

@[simp]
lemma quotientFibreMap_tmul
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens)
    (c : K) (s : Γ((relativeSpace f).obj (ArtinianTest.base A), U)) :
    quotientFibreMap f q W U (c ⊗ₜ[A.algebra] s) =
      c ⊗ₜ[(AQ).algebra] (h).app U s :=
  quotientFibreRingHom_tmul f q W U c s

/-- The tensor map uses the actual quotient section map and actual linear kernel quotient. -/
def quotientTensorMap
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) :
    FibreSections f A U ⊗[K] Kernel q →ₗ[K]
      FibreSections f AQ ((h) ⁻¹ᵁ U) ⊗[K] Kernel r :=
  TensorProduct.map (quotientFibreMap f q W U).toLinearMap
    (ElementaryKernelSubspaceQuotient.kernelLinearMap q W)

@[simp]
lemma quotientTensorMap_tmul
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens)
    (c : K) (s : Γ((relativeSpace f).obj (ArtinianTest.base A), U))
    (x : Kernel q) :
    quotientTensorMap f q W U ((c ⊗ₜ[A.algebra] s) ⊗ₜ[K] x) =
      (c ⊗ₜ[(AQ).algebra] (h).app U s) ⊗ₜ[K]
        ElementaryKernelSubspaceQuotient.kernelLinearMap q W x := by
  simp only [quotientTensorMap, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
    quotientFibreMap_tmul]

/-- On kernel coefficients, the actual section map respects the unchanged
residue-field scalar multiplication. -/
lemma quotient_kernel_section
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens)
    (c : K) (s : Γ((relativeSpace f).obj (ArtinianTest.base A), U))
    (x : Kernel q) :
    (h).app U (testSectionHom f A U (c • x).val * s) =
      testSectionHom f AQ ((h) ⁻¹ᵁ U)
        (c • ElementaryKernelSubspaceQuotient.kernelLinearMap q W x).val *
          (h).app U s := by
  have hx : φ (c • x).val =
      (c • ElementaryKernelSubspaceQuotient.kernelLinearMap q W x).val :=
    congrArg (fun z : Kernel r => z.val)
      ((ElementaryKernelSubspaceQuotient.kernelLinearMap q W).map_smul c x)
  calc
    _ = testSectionHom f AQ ((h) ⁻¹ᵁ U) (φ (c • x).val) * (h).app U s := by
      rw [map_mul, quotient_testSectionHom]
    _ = _ := congrArg (fun a => testSectionHom f AQ ((h) ⁻¹ᵁ U) a * (h).app U s) hx

variable [Flat f]

/-- The actual ideal and tensor quotient maps agree on pure tensors. -/
lemma affineKernelEquiv_quotient_tmul
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen ((h) ⁻¹ᵁ U))
    (c : K) (s : Γ((relativeSpace f).obj (ArtinianTest.base A), U))
    (x : Kernel q) :
    (idealMap f q W).app U
        (affineKernelEquiv f q U hU ((c ⊗ₜ[A.algebra] s) ⊗ₜ[K] x)) =
      affineKernelEquiv f r ((h) ⁻¹ᵁ U) hV
        (quotientTensorMap f q W U ((c ⊗ₜ[A.algebra] s) ⊗ₜ[K] x)) := by
  apply Subtype.ext
  calc
    _ = (h).app U
        (affineKernelEquiv f q U hU ((c ⊗ₜ[A.algebra] s) ⊗ₜ[K] x)).val :=
      idealMap_app f q W U _
    _ = (h).app U (testSectionHom f A U (c • x).val * s) :=
      congrArg ((h).app U) (affineKernelEquiv_tmul f q U hU c s x)
    _ = testSectionHom f AQ ((h) ⁻¹ᵁ U)
        (c • ElementaryKernelSubspaceQuotient.kernelLinearMap q W x).val *
          (h).app U s := quotient_kernel_section f q W U c s x
    _ = (affineKernelEquiv f r ((h) ⁻¹ᵁ U) hV
        ((c ⊗ₜ[(AQ).algebra] (h).app U s) ⊗ₜ[K]
          ElementaryKernelSubspaceQuotient.kernelLinearMap q W x)).val :=
      (affineKernelEquiv_tmul f r ((h) ⁻¹ᵁ U) hV c ((h).app U s)
        (ElementaryKernelSubspaceQuotient.kernelLinearMap q W x)).symm
    _ = _ := congrArg
      (fun t => (affineKernelEquiv f r ((h) ⁻¹ᵁ U) hV t).val)
      (quotientTensorMap_tmul f q W U c s x).symm

private def kernelValueMap
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U) :
    (FibreSections f A U ⊗[K] Kernel q) →+
      Γ((relativeSpace f).obj (ArtinianTest.base A), U) where
  toFun t := (affineKernelEquiv f q U hU t).val
  map_zero' := congrArg (fun z : Γ(idealModule f q, U) => z.val)
    (LinearEquiv.map_zero (affineKernelEquiv f q U hU))
  map_add' a b := congrArg (fun z : Γ(idealModule f q, U) => z.val)
    (LinearEquiv.map_add (affineKernelEquiv f q U hU) a b)

private def viaSection
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U) :
    (FibreSections f A U ⊗[K] Kernel q) →+
      Γ((relativeSpace f).obj (ArtinianTest.base AQ), (h) ⁻¹ᵁ U) :=
  ((h).app U).hom.toAddMonoidHom.comp (kernelValueMap f q U hU)

private def viaTensor
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens)
    (hV : IsAffineOpen ((h) ⁻¹ᵁ U)) :
    (FibreSections f A U ⊗[K] Kernel q) →+
      Γ((relativeSpace f).obj (ArtinianTest.base AQ), (h) ⁻¹ᵁ U) :=
  (kernelValueMap f r ((h) ⁻¹ᵁ U) hV).comp
    (quotientTensorMap f q W U).toAddMonoidHom

private lemma viaSection_eq_viaTensor_tmul
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen ((h) ⁻¹ᵁ U))
    (c : K) (s : Γ((relativeSpace f).obj (ArtinianTest.base A), U)) (x : Kernel q) :
    viaSection f q W U hU ((c ⊗ₜ[A.algebra] s) ⊗ₜ[K] x) =
      viaTensor f q W U hV ((c ⊗ₜ[A.algebra] s) ⊗ₜ[K] x) := by
  change (h).app U
      (affineKernelEquiv f q U hU ((c ⊗ₜ[A.algebra] s) ⊗ₜ[K] x)).val =
    (affineKernelEquiv f r ((h) ⁻¹ᵁ U) hV
      (quotientTensorMap f q W U ((c ⊗ₜ[A.algebra] s) ⊗ₜ[K] x))).val
  calc
    _ = (h).app U (testSectionHom f A U (c • x).val * s) :=
      congrArg ((h).app U) (affineKernelEquiv_tmul f q U hU c s x)
    _ = testSectionHom f AQ ((h) ⁻¹ᵁ U)
        (c • ElementaryKernelSubspaceQuotient.kernelLinearMap q W x).val *
          (h).app U s := quotient_kernel_section f q W U c s x
    _ = (affineKernelEquiv f r ((h) ⁻¹ᵁ U) hV
        ((c ⊗ₜ[(AQ).algebra] (h).app U s) ⊗ₜ[K]
          ElementaryKernelSubspaceQuotient.kernelLinearMap q W x)).val :=
      (affineKernelEquiv_tmul f r ((h) ⁻¹ᵁ U) hV c ((h).app U s)
        (ElementaryKernelSubspaceQuotient.kernelLinearMap q W x)).symm
    _ = _ := congrArg
      (fun t => (affineKernelEquiv f r ((h) ⁻¹ᵁ U) hV t).val)
      (quotientTensorMap_tmul f q W U c s x).symm

private lemma viaSection_eq_viaTensor
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen ((h) ⁻¹ᵁ U)) :
    viaSection f q W U hU = viaTensor f q W U hV :=
  nestedTensor_addHom_ext (viaSection f q W U hU) (viaTensor f q W U hV)
    (viaSection_eq_viaTensor_tmul f q W U hU hV)

/-- The actual ideal quotient map agrees with the actual affine tensor map. -/
lemma affineKernelEquiv_quotient
    (U : ((relativeSpace f).obj (ArtinianTest.base A)).Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen ((h) ⁻¹ᵁ U))
    (t : FibreSections f A U ⊗[K] Kernel q) :
    (idealMap f q W).app U (affineKernelEquiv f q U hU t) =
      affineKernelEquiv f r ((h) ⁻¹ᵁ U) hV (quotientTensorMap f q W U t) := by
  apply Subtype.ext
  calc
    _ = (h).app U (affineKernelEquiv f q U hU t).val := idealMap_app f q W U _
    _ = _ := DFunLike.congr_fun (viaSection_eq_viaTensor f q W U hU hV) t

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianKernelQuotientTensor
