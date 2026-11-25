/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdIntegralScalarLiftProperty
public import WeilConjectures.SixFunctors.RamifiedPullback.TensorProof.RamifiedFiniteTensorSections
import WeilConjectures.AlgebraicGeometry.InternalSectionTotalComparison
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
import all WeilConjectures.TraceFormula.Integral.IntegralScalarOrdinaryModelComparison

/-! # Module-level coherence of the ordinary coefficient transport

The ordinary coefficient transport is normalized on unit tensor sections. It is therefore
compatible with tensor balancing (on both sides) and with the multiplication units.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
namespace WeilConjectures.FdIntegralScalarForward

section PbcTensor

variable {T : Scheme.{u}} {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)

private local instance pbcAbSheafify : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, 0} T

private local instance pbcAbBijective :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T

/-- Unit tensor sections detect maps out of the ordinary PBC scalar extension. -/
theorem pbcTensor_ext (M : pbcModules T R) (N : pbcModules T S)
    (f g : (pbcExtend φ).obj M ⟶ N)
    (h : ∀ (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      f.val.app U (pbcTensorSection φ M U 1 x) = g.val.app U (pbcTensorSection φ M U 1 x)) :
    f = g := by
  haveI : HasWeakSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    (WeilConjectures.integralCoefficientAbSheafify.{u, 0} T).isRightAdjoint
  haveI := WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  haveI := AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.sectionRingHasSheafCompose
    (ProEt.topology T)
  exact RamifiedPullback.TensorProof.tensorSection_ext.{u + 1, u, u + 1} φ (pbcExtend φ)
    (pbcExtensionExistence φ).choose_spec.choose M N f g h

/-- Naturality of PBC tensor sections. -/
theorem pbcTensor_map {M N : pbcModules T R} (f : M ⟶ N) (U : T.ProEtᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    ((pbcExtend φ).map f).val.app U (pbcTensorSection φ M U s x) =
      pbcTensorSection φ N U s (f.val.app U x) := by
  haveI : HasWeakSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    (WeilConjectures.integralCoefficientAbSheafify.{u, 0} T).isRightAdjoint
  haveI := WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  haveI := AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.sectionRingHasSheafCompose
    (ProEt.topology T)
  exact RamifiedPullback.TensorProof.tensorSection_map.{u + 1, u, u + 1} φ (pbcExtend φ)
    (pbcExtensionExistence φ).choose_spec.choose
    (fun f ↦ (pbcExtensionExistence φ).choose_spec.choose_spec.choose f) f U s x

/-- The unit of the ordinary PBC adjunction is the unit tensor section. -/
theorem pbcScalarAdjunction_unit (M : pbcModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcScalarAdjunction φ).unit.app M).val.app U x = pbcTensorSection φ M U 1 x :=
  (pbcScalarAdjunction_exists φ).exists.choose_spec M U x

/-- Maps out of an iterated PBC scalar extension are detected on iterated unit tensors. -/
theorem pbcTensor_ext₂ {B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (ψ : S ⟶ B)
    (M : pbcModules T R) (N : pbcModules T B)
    (f g : (pbcExtend ψ).obj ((pbcExtend φ).obj M) ⟶ N)
    (h : ∀ (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      f.val.app U (pbcTensorSection ψ _ U 1 (pbcTensorSection φ M U 1 x)) =
        g.val.app U (pbcTensorSection ψ _ U 1 (pbcTensorSection φ M U 1 x))) :
    f = g := by
  apply ((pbcScalarAdjunction ψ).homEquiv _ _).injective
  apply pbcTensor_ext φ
  intro U x
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change f.val.app U (((pbcScalarAdjunction ψ).unit.app _).val.app U _) =
    g.val.app U (((pbcScalarAdjunction ψ).unit.app _).val.app U _)
  rw [pbcScalarAdjunction_unit]
  exact h U x

variable {B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (ψ : S ⟶ B) (χ : R ⟶ B)
  (hc : φ ≫ ψ = χ)

/-- Tensor balancing for ordinary PBC scalar extensions: the mate of the identity-on-sections
composition of scalar restrictions. -/
def pbcExtendComp : pbcExtend φ ⋙ pbcExtend ψ ≅ pbcExtend χ :=
  Adjunction.leftAdjointCompIso (pbcScalarAdjunction φ) (pbcScalarAdjunction ψ)
    (pbcScalarAdjunction χ) (pbcRestrictComp φ ψ χ hc)

theorem pbcRestrictComp_inv_section (M : pbcModules T B) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp φ ψ χ hc).inv.app M).val.app U x = x := by
  have h1 := (pbcRestrictComp_exists φ ψ χ hc).exists.choose_spec M U
    (((pbcRestrictComp φ ψ χ hc).inv.app M).val.app U x)
  have h2 := congrArg (fun f ↦ f.val.app U x) ((pbcRestrictComp φ ψ χ hc).inv_hom_id_app M)
  exact h1.symm.trans h2

/-- Tensor balancing on iterated unit tensors. -/
theorem pbcExtendComp_tensor (M : pbcModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcExtendComp φ ψ χ hc).hom.app M).val.app U
        (pbcTensorSection ψ _ U 1 (pbcTensorSection φ M U 1 x)) =
      pbcTensorSection χ M U 1 x := by
  have h := unit_conjugateEquiv_symm (pbcScalarAdjunction χ)
    ((pbcScalarAdjunction φ).comp (pbcScalarAdjunction ψ)) (pbcRestrictComp φ ψ χ hc).inv M
  have h' := congrArg (fun f ↦ f.val.app U x) h
  change ((pbcRestrictComp φ ψ χ hc).inv.app _).val.app U
      (((pbcScalarAdjunction χ).unit.app M).val.app U x) =
    ((pbcExtendComp φ ψ χ hc).hom.app M).val.app U
      (((pbcScalarAdjunction ψ).unit.app ((pbcExtend φ).obj M)).val.app U
        (((pbcScalarAdjunction φ).unit.app M).val.app U x)) at h'
  rw [pbcRestrictComp_inv_section, pbcScalarAdjunction_unit, pbcScalarAdjunction_unit,
    pbcScalarAdjunction_unit] at h'
  exact h'.symm

end PbcTensor

end WeilConjectures.FdIntegralScalarForward

namespace WeilConjectures.FdIntegralScalarForward

section Ordinary

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u})

set_option hygiene false in
/-- The ordinary integral scalar extension in the stage presentation. -/
local notation "𝒪 " h:max => integralOrdinaryScalar l (pbcFiniteField.{u} l Ω _)
  (pbcFiniteField.{u} l Ω _) (pbcFiniteFieldInclusion l Ω h) T

set_option hygiene false in
/-- The coefficient transport in the stage presentation. -/
local notation "𝓉 " E:max => fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T

set_option hygiene false in
/-- The ordinary PBC scalar extension. -/
local notation "𝒳 " h:max => pbcExtend (pbcCompletedScalarMap l Ω T h)

/-- The ordinary comparison square, through the canonical ordinary scalar model. -/
private def oc {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (o : FdOrdinaryScalarTransport l Ω T h) :
    𝒪 h ⋙ 𝓉 L ≅ 𝓉 E ⋙ 𝒳 h :=
  Functor.isoWhiskerRight (ordinaryScalarModelIso l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T) (𝓉 L) ≪≫
    o.comparison

private theorem oc_hom_tensor {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (o : FdOrdinaryScalarTransport l Ω T h)
    (M : integralTowerModules l (pbcFiniteField.{u} l Ω E) T) (U : T.ProEtᵒᵖ)
    (x : M.val.obj U) :
    ((oc l Ω T h o).hom.app M).val.app U
        (integralOrdinaryTensorSection l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
          (pbcFiniteFieldInclusion l Ω h) T M U 1 x) =
      pbcTensorSection (pbcCompletedScalarMap l Ω T h) ((𝓉 E).obj M) U 1 x := by
  change (o.comparison.hom.app M).val.app U
    (((ordinaryScalarModelIso l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
      (pbcFiniteFieldInclusion l Ω h) T).hom.app M).val.app U
      (integralOrdinaryTensorSection l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
          (pbcFiniteFieldInclusion l Ω h) T M U 1 x)) = _
  rw [scalarModelTensor, o.generators, map_one]

private theorem oc_inv_tensor {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (o : FdOrdinaryScalarTransport l Ω T h)
    (M : integralTowerModules l (pbcFiniteField.{u} l Ω E) T) (U : T.ProEtᵒᵖ)
    (x : M.val.obj U) :
    ((oc l Ω T h o).inv.app M).val.app U
        (pbcTensorSection (pbcCompletedScalarMap l Ω T h) ((𝓉 E).obj M) U 1 x) =
      integralOrdinaryTensorSection l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
          (pbcFiniteFieldInclusion l Ω h) T M U 1 x := by
  rw [← oc_hom_tensor l Ω T h o]
  exact congrArg (fun f ↦ f.val.app U (integralOrdinaryTensorSection l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T M U 1 x))
    ((oc l Ω T h o).hom_inv_id_app M)

/-- Composite of the actual field inclusions. -/
theorem inclusion_comp {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M) :
    (pbcFiniteFieldInclusion.{u} l Ω k).comp (pbcFiniteFieldInclusion.{u} l Ω h) =
      pbcFiniteFieldInclusion.{u} l Ω (h.trans k) :=
  (AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k

/-- The identity field inclusion. -/
theorem inclusion_id (E : Padic.FiniteCoefficientFields l Ω) :
    pbcFiniteFieldInclusion.{u} l Ω (le_refl E) = AlgHom.id ℚ_[l] (pbcFiniteField.{u} l Ω E) :=
  (AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).1 E

/-- Ordinary tensor balancing with the direct field inclusion. -/
def Ocomp {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M) :
    𝒪 h ⋙ 𝒪 k ≅ 𝒪 (h.trans k) :=
  integralOrdinaryScalarComp l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
      (pbcFiniteFieldInclusion l Ω h) T (pbcFiniteField.{u} l Ω M)
      (pbcFiniteFieldInclusion l Ω k) ≪≫
    eqToIso (congrArg (fun ι ↦ integralOrdinaryScalar l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω M) ι T) (inclusion_comp l Ω h k))

/-- The ordinary unit with the identity field inclusion. -/
def Ounit (E : Padic.FiniteCoefficientFields l Ω) : 𝒪 (le_refl E) ≅ 𝟭 _ :=
  eqToIso (congrArg (fun ι ↦ integralOrdinaryScalar l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω E) ι T) (inclusion_id l Ω E)) ≪≫
    integralOrdinaryScalarUnit l (pbcFiniteField.{u} l Ω E) T

private theorem eqToIso_tensor
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    {ι ι' : E →ₐ[ℚ_[l]] L} (hι : ι = ι') (N : integralTowerModules l E T) (U : T.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l L T).obj.obj U) (x : N.val.obj U) :
    ((eqToIso (congrArg (fun ι ↦ integralOrdinaryScalar l E L ι T) hι)).hom.app N).val.app U
        (integralOrdinaryTensorSection l E L ι T N U s x) =
      integralOrdinaryTensorSection l E L ι' T N U s x := by
  subst hι
  rfl

private theorem comp_section {C : Type*} [Category C] {J : GrothendieckTopology C}
    {Rg : Sheaf J RingCat.{u + 1}} {A B D : SheafOfModules.{u + 1} Rg} (f : A ⟶ B) (g : B ⟶ D)
    (U : Cᵒᵖ) (z : A.val.obj U) : (f ≫ g).val.app U z = g.val.app U (f.val.app U z) := rfl

private theorem gcomp_tensor
    (E L M : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] M) (k : E →ₐ[ℚ_[l]] M) (hk : j.comp ι = k)
    (N : integralTowerModules l E T) (U : T.ProEtᵒᵖ) (x : N.val.obj U) :
    ((integralOrdinaryScalarComp l E L ι T M j ≪≫
        eqToIso (congrArg (fun ι ↦ integralOrdinaryScalar l E M ι T) hk)).hom.app N).val.app U
        (integralOrdinaryTensorSection l L M j T _ U 1
          (integralOrdinaryTensorSection l E L ι T N U 1 x)) =
      integralOrdinaryTensorSection l E M k T N U 1 x := by
  subst hk
  rw [eqToIso_refl, Iso.trans_refl]
  unfold integralOrdinaryScalarComp
  rw [(integralOrdinaryScalarComp_existsUnique l E L ι T M j).exists.choose_spec, map_one,
    one_mul]

private theorem gunit_tensor
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (N : integralTowerModules l E T) (U : T.ProEtᵒᵖ) (x : N.val.obj U) :
    ((integralOrdinaryScalarUnit l E T).hom.app N).val.app U
        (integralOrdinaryTensorSection l E E (AlgHom.id ℚ_[l] E) T N U 1 x) = x :=
  ((integralOrdinaryScalarUnit_existsUnique l E T).exists.choose_spec N U 1 x).trans
    (one_smul _ x)

theorem Ocomp_eq {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M) :
    Ocomp l Ω T h k = integralOrdinaryScalarComp l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω L)
      (pbcFiniteFieldInclusion l Ω h) T (pbcFiniteField.{u} l Ω M)
      (pbcFiniteFieldInclusion l Ω k) ≪≫
    eqToIso (congrArg (fun ι ↦ integralOrdinaryScalar l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω M) ι T) (inclusion_comp l Ω h k)) := rfl

theorem Ocomp_app_eq {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M)
    (N : integralTowerModules l (pbcFiniteField.{u} l Ω E) T) :
    (Ocomp l Ω T h k).hom.app N = (integralOrdinaryScalarComp l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω L)
      (pbcFiniteFieldInclusion l Ω h) T (pbcFiniteField.{u} l Ω M)
      (pbcFiniteFieldInclusion l Ω k) ≪≫
    eqToIso (congrArg (fun ι ↦ integralOrdinaryScalar l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω M) ι T) (inclusion_comp l Ω h k))).hom.app N := by rw [Ocomp_eq]

theorem Ocomp_tensor {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M)
    (N : integralTowerModules l (pbcFiniteField.{u} l Ω E) T) (U : T.ProEtᵒᵖ)
    (x : N.val.obj U) :
    ((Ocomp l Ω T h k).hom.app N).val.app U
        (integralOrdinaryTensorSection l _ _ (pbcFiniteFieldInclusion l Ω k) T _ U 1
          (integralOrdinaryTensorSection l _ _ (pbcFiniteFieldInclusion l Ω h) T N U 1 x)) =
      integralOrdinaryTensorSection l _ _ (pbcFiniteFieldInclusion l Ω (h.trans k)) T N U 1 x := by
  rw [Ocomp_app_eq]
  exact gcomp_tensor l T _ _ _ _ _ _ (inclusion_comp l Ω h k) N U x

theorem Ounit_eq (E : Padic.FiniteCoefficientFields l Ω) :
    Ounit l Ω T E = eqToIso (congrArg (fun ι ↦ integralOrdinaryScalar l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω E) ι T) (inclusion_id l Ω E)) ≪≫
    integralOrdinaryScalarUnit l (pbcFiniteField.{u} l Ω E) T := rfl

theorem Ounit_app_eq (E : Padic.FiniteCoefficientFields l Ω)
    (N : integralTowerModules l (pbcFiniteField.{u} l Ω E) T) :
    (Ounit l Ω T E).hom.app N = (eqToIso (congrArg (fun ι ↦ integralOrdinaryScalar l
      (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω E) ι T) (inclusion_id l Ω E)) ≪≫
      integralOrdinaryScalarUnit l (pbcFiniteField.{u} l Ω E) T).hom.app N := by
  rw [Ounit_eq]

theorem Ounit_tensor (E : Padic.FiniteCoefficientFields l Ω)
    (N : integralTowerModules l (pbcFiniteField.{u} l Ω E) T) (U : T.ProEtᵒᵖ)
    (x : N.val.obj U) :
    ((Ounit l Ω T E).hom.app N).val.app U
        (integralOrdinaryTensorSection l _ _ (pbcFiniteFieldInclusion l Ω (le_refl E)) T N U
          1 x) = x := by
  rw [Ounit_app_eq, Iso.trans_hom, NatTrans.comp_app, comp_section,
    eqToIso_tensor l T _ _ (inclusion_id l Ω E) N U 1 x]
  exact gunit_tensor l T _ N U x

variable [IsNoetherian T]

/-- Tensor balancing of the ordinary PBC scalar extensions along field inclusions. -/
def Xcomp {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M) :
    𝒳 h ⋙ 𝒳 k ≅ 𝒳 (h.trans k) :=
  pbcExtendComp _ _ _ (pbcCompletedScalarMap_comp l Ω T h k)

theorem Xcomp_tensor {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M)
    (N : pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) (U : T.ProEtᵒᵖ)
    (x : N.val.obj U) :
    ((Xcomp l Ω T h k).hom.app N).val.app U
        (pbcTensorSection (pbcCompletedScalarMap l Ω T k) _ U 1
          (pbcTensorSection (pbcCompletedScalarMap l Ω T h) N U 1 x)) =
      pbcTensorSection (pbcCompletedScalarMap l Ω T (h.trans k)) N U 1 x :=
  pbcExtendComp_tensor _ _ _ _ N U x

omit [AlgebraicGeometry.IsNoetherian T] in
/-- Tensor-normalized comparisons are compatible with tensor balancing. The comparisons and
balancing maps are arbitrary isomorphisms characterized on unit tensors. -/
theorem comparison_cocycle {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M)
    (ch : 𝒪 h ⋙ 𝓉 L ≅ 𝓉 E ⋙ 𝒳 h) (ck : 𝒪 k ⋙ 𝓉 M ≅ 𝓉 L ⋙ 𝒳 k)
    (chk : 𝒪 (h.trans k) ⋙ 𝓉 M ≅ 𝓉 E ⋙ 𝒳 (h.trans k))
    (Oc : 𝒪 h ⋙ 𝒪 k ≅ 𝒪 (h.trans k)) (Xc : 𝒳 h ⋙ 𝒳 k ≅ 𝒳 (h.trans k))
    (hch : ∀ N U x, (ch.inv.app N).val.app U
      (pbcTensorSection (pbcCompletedScalarMap l Ω T h) ((𝓉 E).obj N) U 1 x) =
        integralOrdinaryTensorSection l _ _ (pbcFiniteFieldInclusion l Ω h) T N U 1 x)
    (hck : ∀ N U x, (ck.inv.app N).val.app U
      (pbcTensorSection (pbcCompletedScalarMap l Ω T k) ((𝓉 L).obj N) U 1 x) =
        integralOrdinaryTensorSection l _ _ (pbcFiniteFieldInclusion l Ω k) T N U 1 x)
    (hchk : ∀ N U x, (chk.inv.app N).val.app U
      (pbcTensorSection (pbcCompletedScalarMap l Ω T (h.trans k)) ((𝓉 E).obj N) U 1 x) =
        integralOrdinaryTensorSection l _ _ (pbcFiniteFieldInclusion l Ω (h.trans k)) T N U 1 x)
    (hOc : ∀ N U x, (Oc.hom.app N).val.app U
        (integralOrdinaryTensorSection l _ _ (pbcFiniteFieldInclusion l Ω k) T _ U 1
          (integralOrdinaryTensorSection l _ _ (pbcFiniteFieldInclusion l Ω h) T N U 1 x)) =
      integralOrdinaryTensorSection l _ _ (pbcFiniteFieldInclusion l Ω (h.trans k)) T N U 1 x)
    (hXc : ∀ N U x, (Xc.hom.app N).val.app U
        (pbcTensorSection (pbcCompletedScalarMap l Ω T k) _ U 1
          (pbcTensorSection (pbcCompletedScalarMap l Ω T h) N U 1 x)) =
      pbcTensorSection (pbcCompletedScalarMap l Ω T (h.trans k)) N U 1 x)
    (N : integralTowerModules l (pbcFiniteField.{u} l Ω E) T) :
    (𝒳 k).map (ch.inv.app N) ≫ ck.inv.app ((𝒪 h).obj N) ≫ (𝓉 M).map (Oc.hom.app N) =
      Xc.hom.app ((𝓉 E).obj N) ≫ chk.inv.app N := by
  apply pbcTensor_ext₂
  intro U x
  have e1 : ((𝒳 k).map (ch.inv.app N)).val.app U
      (pbcTensorSection (pbcCompletedScalarMap l Ω T k) _ U 1
        (pbcTensorSection (pbcCompletedScalarMap l Ω T h) ((𝓉 E).obj N) U 1 x)) =
      pbcTensorSection (pbcCompletedScalarMap l Ω T k) ((𝓉 L).obj ((𝒪 h).obj N)) U 1
        (integralOrdinaryTensorSection l _ _ (pbcFiniteFieldInclusion l Ω h) T N U 1 x) := by
    rw [pbcTensor_map, hch]
    rfl
  rw [comp_section, comp_section, comp_section]
  exact (congrArg (fun y ↦ (((𝓉 M).map (Oc.hom.app N)).val.app U)
    (((ck.inv.app ((𝒪 h).obj N))).val.app U y)) e1).trans
    ((congrArg (fun y ↦ (((𝓉 M).map (Oc.hom.app N)).val.app U) y) (hck _ U _)).trans
    ((hOc N U x).trans ((congrArg (fun y ↦ (chk.inv.app N).val.app U y)
      (hXc _ U x)).trans (hchk N U x)).symm))

omit [AlgebraicGeometry.IsNoetherian T] in
/-- Tensor-normalized comparisons are compatible with the multiplication units. -/
theorem comparison_unit (E : Padic.FiniteCoefficientFields l Ω)
    (c : 𝒪 (le_refl E) ⋙ 𝓉 E ≅ 𝓉 E ⋙ 𝒳 (le_refl E)) (Ou : 𝒪 (le_refl E) ≅ 𝟭 _)
    (Xu : 𝒳 (le_refl E) ≅ 𝟭 _)
    (hc : ∀ N U x, (c.inv.app N).val.app U
      (pbcTensorSection (pbcCompletedScalarMap l Ω T (le_refl E)) ((𝓉 E).obj N) U 1 x) =
        integralOrdinaryTensorSection l _ _ (pbcFiniteFieldInclusion l Ω (le_refl E)) T N U 1 x)
    (hOu : ∀ N U x, (Ou.hom.app N).val.app U
      (integralOrdinaryTensorSection l _ _ (pbcFiniteFieldInclusion l Ω (le_refl E)) T N U
        1 x) = x)
    (hXu : ∀ N U x, (Xu.hom.app N).val.app U
      (pbcTensorSection (pbcCompletedScalarMap l Ω T (le_refl E)) N U 1 x) = x)
    (N : integralTowerModules l (pbcFiniteField.{u} l Ω E) T) :
    c.inv.app N ≫ (𝓉 E).map (Ou.hom.app N) = Xu.hom.app ((𝓉 E).obj N) := by
  apply pbcTensor_ext
  intro U x
  rw [comp_section]
  exact (congrArg (fun y ↦ (((𝓉 E).map (Ou.hom.app N)).val.app U) y) (hc N U x)).trans
    ((hOu N U x).trans (hXu _ U x).symm)

theorem Xunit_tensor (E : Padic.FiniteCoefficientFields l Ω)
    (N : pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) (U : T.ProEtᵒᵖ)
    (x : N.val.obj U) :
    ((pbcOrdinaryScalarUnit l Ω T E).hom.app N).val.app U
      (pbcTensorSection (pbcCompletedScalarMap l Ω T (le_refl E)) N U 1 x) = x :=
  ((pbcOrdinaryScalarUnit_exists l Ω T E).exists.choose_spec N U 1 x).trans (one_smul _ _)

end Ordinary
end WeilConjectures.FdIntegralScalarForward
