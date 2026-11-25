/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothBaseChange.SbcCompletedOperations
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarAmbientOperations
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationLift

/-! # Canonical raw ambient scalar system

Source: literature/blueprint/slopmaster2/src/version/sketch/32_smooth_base_change.tex,
lines 1191--1228 and 1291--1338
(blueprint: def-sbc-ambient-complete-raw-scalar-system).

## Main definitions

* `pbcAmbientCompleteStage`: the raw rational ambient complete category.
* `pbcAmbientCompleteRawTransition`: the normalized localized tensor.
* `pbcAmbientCompleteRawSystem`: these tensors and their balanced associators.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

universe u v
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- Use the existing division-ring torsion-free instance directly for coefficient fields.
This specializes Mathlib's instance, avoiding its slower flatness search path.
Source: sketch32, coefficient fields throughout lines 1191--1438;
Mathlib `DivisionSemiring.to_moduleIsTorsionFree`
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
instance (priority := 3000) pbcCompleteCoefficientTorsionFree
    (l : ℕ) [Fact l.Prime] (L : Type v) [Field L] [Algebra (Padic l) L] :
    Module.IsTorsionFree (Padic l) L := DivisionSemiring.to_moduleIsTorsionFree

/-- The ambient complete coefficient stage before idempotent completion.
Source: sketch32, lines 1192--1207 (blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
def pbcAmbientCompleteStage (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) : Type (u + 2) :=
  WeilConjectures.PbcRationalComplete l (pbcFiniteField.{u} l Ω E) W

/-- Name the existing category structure on the unchanged raw ambient stage.
Source: sketch32, lines 1192--1207
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
noncomputable instance pbcAmbientCompleteStageCategory
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) :
    Category (pbcAmbientCompleteStage l Ω W E) :=
  inferInstanceAs (Category (WeilConjectures.PbcRationalComplete
    l (pbcFiniteField.{u} l Ω E) W))

/-- The existing addition on raw ambient arrows, through the named category instance.
Source: sketch32, lines 1192--1207
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
noncomputable instance pbcAmbientCompleteStagePreadditive
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) :
    Preadditive (pbcAmbientCompleteStage l Ω W E) :=
  inferInstanceAs (Preadditive (WeilConjectures.PbcRationalComplete
    l (pbcFiniteField.{u} l Ω E) W))

variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
  [IsNoetherian W]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
  [hInv : Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]

variable {E F G : Padic.FiniteCoefficientFields l Ω}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsNoetherian W] hDim hInv in
/-- The recorded ambient tensor is the scalar tensor along the transported field inclusion. -/
private theorem pbcAmbientScalarExtension_eq (h : E ≤ F) :
    pbcAmbientScalarExtension l Ω W h =
      pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteFieldInclusion l Ω h) W := by
  simp only [pbcAmbientScalarExtension, pbcEmbeddingAmbientTensor,
    pbcStageCoefficientMap_eq l Ω W h]

-- Keep the recorded base hypotheses in the public signature.
set_option linter.unusedSectionVars false in
/-- Finite coefficient tensor preserves intrinsic completeness without constructible bounds.
Source: sketch32, finite-stage pair categories, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system).
Proof: finite freeness makes tensor commute with the Koszul completion limit.
The source and target uniformizer powers are cofinal. Thus tensor carries the
invertible source completion unit to the target completion unit. -/
theorem pbcAmbientCompleteTensor_preserves (h : E ≤ F)
    (K : WeilConjectures.PbcComplete l (pbcFiniteField.{u} l Ω E) W) :
    WeilConjectures.IsPbcComplete l (pbcFiniteField.{u} l Ω F) W
      ((pbcAmbientScalarExtension l Ω W h).obj K.obj) := by
  rw [pbcAmbientScalarExtension_eq l Ω W h]
  exact pbcScalarPreservesComplete l _ _ (pbcFiniteFieldInclusion l Ω h) W K

/-- Restrict the actual finite-projection-normalized tensor to complete objects.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
@[irreducible] def pbcAmbientCompleteIntegralTransition (h : E ≤ F) :
    WeilConjectures.PbcComplete l (pbcFiniteField.{u} l Ω E) W ⥤
      WeilConjectures.PbcComplete l (pbcFiniteField.{u} l Ω F) W :=
  ObjectProperty.lift (WeilConjectures.IsPbcComplete l (pbcFiniteField.{u} l Ω F) W)
    (ObjectProperty.ι (WeilConjectures.IsPbcComplete l (pbcFiniteField.{u} l Ω E) W) ⋙
      pbcAmbientScalarExtension l Ω W h)
    (pbcAmbientCompleteTensor_preserves l Ω W h)

/-- Localization of the complete integral stage; no idempotents are adjoined.
Source: sketch32, lines 1192--1207
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
abbrev pbcAmbientCompleteLocalization (E : Padic.FiniteCoefficientFields l Ω) :=
  ScalarLocalization.localization (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (WeilConjectures.PbcComplete l (pbcFiniteField.{u} l Ω E) W)
    (pbcStageUniformizer.{u} l Ω E)

section Construction

attribute [local semireducible] pbcAmbientCompleteIntegralTransition
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv

omit [IsNoetherian W] hDim hInv in
/-- The ambient tensor is additive, as a left adjoint. -/
private theorem pbcAmbientScalarExtension_additive (h : E ≤ F) :
    (pbcAmbientScalarExtension l Ω W h).Additive := by
  have : (pbcDerivedRestrict (pbcCompletedScalarMap l Ω W h)).Additive := by
    dsimp only [pbcDerivedRestrict]
    infer_instance
  exact (pbcDerivedScalarAdjunction _).left_adjoint_additive

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsNoetherian W] hDim hInv in
/-- The ambient tensor is semilinear along the inclusion of integer rings. -/
private theorem pbcAmbientScalarExtension_smul (h : E ≤ F)
    {K L : PbcCompletedDerived W (pbcStageDatum.{u} l Ω E)}
    (a : PbcIntegralRing l (pbcFiniteField.{u} l Ω E)) (f : K ⟶ L) :
    (pbcAmbientScalarExtension l Ω W h).map (a • f) =
      pbcIntegerInclusion l Ω h a • (pbcAmbientScalarExtension l Ω W h).map f := by
  rw [pbcAmbientScalarExtension_eq l Ω W h]
  exact scalarAdjunction (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l _ _
      (pbcFiniteFieldInclusion l Ω h) W)) a (pbcIntegerInclusion l Ω h a)
    (scalarExactDerived (pbcRestrict (pbcScalarCoefficientMap l _ _
      (pbcFiniteFieldInclusion l Ω h) W)) (pbcIntegerInclusion l Ω h a) a
      (scalarRestrict l _ _ (pbcFiniteFieldInclusion l Ω h) W a)) K L f

/-- The complete integral tensor is additive. -/
private instance pbcAmbientCompleteIntegralTransition_additive (h : E ≤ F) :
    (pbcAmbientCompleteIntegralTransition l Ω W h).Additive where
  map_add {_ _} {_ _} := by
    have := pbcAmbientScalarExtension_additive l Ω W h
    apply ObjectProperty.hom_ext
    exact (pbcAmbientScalarExtension l Ω W h).map_add

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The complete integral tensor is semilinear along the inclusion of integer rings. -/
private theorem pbcAmbientCompleteIntegralTransition_semilinear (h : E ≤ F) :
    ScalarLocalization.IsSemilinear (pbcIntegerInclusion l Ω h)
      (pbcAmbientCompleteIntegralTransition l Ω W h) := by
  intro K L a f
  apply ObjectProperty.hom_ext
  exact pbcAmbientScalarExtension_smul l Ω W h a f.hom

section
attribute [-instance] ULift.module

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsAlgClosure (Padic l) Ω] in
/-- The source uniformizer becomes a unit in the target rational coefficients. -/
private theorem pbcStageUniformizer_isUnit (h : E ≤ F) :
    IsUnit (algebraMap (PbcIntegralRing l (pbcFiniteField.{u} l Ω F))
      (Localization.Away (pbcStageUniformizer.{u} l Ω F))
        (pbcIntegerInclusion l Ω h (pbcStageUniformizer.{u} l Ω E))) := by
  let k : Localization.Away (pbcStageUniformizer.{u} l Ω E) →+*
      Localization.Away (pbcStageUniformizer.{u} l Ω F) :=
    (pbcRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω F)).symm.toRingHom.comp
      ((pbcFiniteFieldInclusion l Ω h).toRingHom.comp
        (pbcRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω E)).toRingHom)
  have hc : k (algebraMap _ _ (pbcStageUniformizer.{u} l Ω E)) =
      algebraMap (PbcIntegralRing l (pbcFiniteField.{u} l Ω F))
        (Localization.Away (pbcStageUniformizer.{u} l Ω F))
        (pbcIntegerInclusion l Ω h (pbcStageUniformizer.{u} l Ω E)) := by
    apply (pbcRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω F)).injective
    simp only [k, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.apply_symm_apply, scalarRationalCoefficient]
    rfl
  rw [← hc]
  exact (IsLocalization.Away.algebraMap_isUnit (pbcStageUniformizer.{u} l Ω E)).map k

end

/-- The semilinear extension of the complete integral tensor to fractions. -/
private def pbcAmbientCompleteRawExtension (h : E ≤ F) :
    pbcAmbientCompleteStage l Ω W E ⥤ pbcAmbientCompleteStage l Ω W F :=
  ScalarLocalization.extension (pbcStageUniformizer.{u} l Ω E)
    (pbcStageUniformizer.{u} l Ω F) (pbcIntegerInclusion l Ω h)
    (pbcStageUniformizer_isUnit l Ω h) (pbcAmbientCompleteIntegralTransition l Ω W h)
    (pbcAmbientCompleteIntegralTransition_semilinear l Ω W h)

private theorem pbcAmbientCompleteRawExtension_spec (h : E ≤ F) :
    pbcAmbientCompleteLocalization l Ω W E ⋙ pbcAmbientCompleteRawExtension l Ω W h =
      pbcAmbientCompleteIntegralTransition l Ω W h ⋙
        pbcAmbientCompleteLocalization l Ω W F :=
  (ScalarLocalization.extension_spec _ _ _ _ _ _).2.1

private theorem pbcAmbientCompleteRawExtension_additive (h : E ≤ F) :
    (pbcAmbientCompleteRawExtension l Ω W h).Additive :=
  ScalarLocalization.extensionAdditive _ _ _ _ _ _

/-- The rational tensor functor is uniquely determined on integral objects and arrows.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system).
Proof: the coefficient inclusion sends a source uniformizer to a unit times a
positive power of the target uniformizer. Send a fraction to the tensor image
with its denominator mapped by that inclusion. Bilinearity gives the tensor-Hom
formula, functoriality descends, and fractions generate every Hom, proving uniqueness. -/
theorem pbcAmbientCompleteRaw_exists (h : E ≤ F) :
    ∃! T : pbcAmbientCompleteStage l Ω W E ⥤ pbcAmbientCompleteStage l Ω W F,
      pbcAmbientCompleteLocalization l Ω W E ⋙ T =
        pbcAmbientCompleteIntegralTransition l Ω W h ⋙
          pbcAmbientCompleteLocalization l Ω W F :=
  ⟨pbcAmbientCompleteRawExtension l Ω W h, pbcAmbientCompleteRawExtension_spec l Ω W h,
    fun _ hB ↦ ScalarLocalization.functor_ext
      (hB.trans (pbcAmbientCompleteRawExtension_spec l Ω W h).symm)⟩

/-- Canonical rational tensor, normalized to the literal identity at equal fields.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
@[irreducible] def pbcAmbientCompleteRawTransition (h : E ≤ F) :
    pbcAmbientCompleteStage l Ω W E ⥤ pbcAmbientCompleteStage l Ω W F := by
  classical
  exact if e : E = F then e ▸ 𝟭 _ else
    (pbcAmbientCompleteRaw_exists l Ω W h).exists.choose

private theorem pbcAmbientCompleteRawTransition_refl (h : E ≤ E) :
    pbcAmbientCompleteRawTransition l Ω W h = 𝟭 _ := by
  simp [pbcAmbientCompleteRawTransition]

private theorem pbcAmbientCompleteRawTransition_of_ne (h : E ≤ F) (hEF : E ≠ F) :
    pbcAmbientCompleteRawTransition l Ω W h =
      (pbcAmbientCompleteRaw_exists l Ω W h).exists.choose := by
  simp [pbcAmbientCompleteRawTransition, hEF]

/-- The complete integral tensor unit is the restriction of the canonical derived unit.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system).
Proof: the ambient unit is normalized on tensor sections. Completeness is a full
subcategory, so lift its components and inverses. Faithfulness proves uniqueness. -/
theorem pbcAmbientCompleteIntegralUnit_exists (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! e : pbcAmbientCompleteIntegralTransition l Ω W (le_refl E) ≅ 𝟭 _,
      HEq (Functor.whiskerRight e.hom
          (ObjectProperty.ι (WeilConjectures.IsPbcComplete l (pbcFiniteField.{u} l Ω E) W)))
        (Functor.whiskerLeft
          (ObjectProperty.ι (WeilConjectures.IsPbcComplete l (pbcFiniteField.{u} l Ω E) W))
          (pbcAmbientScalarUnit l Ω W E).hom) := by
  let e : pbcAmbientCompleteIntegralTransition l Ω W (le_refl E) ≅ 𝟭 _ :=
    NatIso.ofComponents
      (fun K ↦ ObjectProperty.isoMk _ ((pbcAmbientScalarUnit l Ω W E).app K.obj))
      (fun f ↦ by
        apply ObjectProperty.hom_ext
        exact (pbcAmbientScalarUnit l Ω W E).hom.naturality f.hom)
  refine ⟨e, HEq.rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact congrArg (fun η ↦ η.app K) (eq_of_heq he')

/-- The section-normalized complete tensor unit.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
@[irreducible] def pbcAmbientCompleteIntegralUnit (E : Padic.FiniteCoefficientFields l Ω) :=
  (pbcAmbientCompleteIntegralUnit_exists l Ω W E).exists.choose

/-- Integral normalization of raw rational extension, including the equal-field branch.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system).
Proof: at equal fields use the inverse tensor unit. At distinct fields use the
unique localization factorization. These formulas fix every component. -/
theorem pbcAmbientCompleteIntegralComparison_exists (h : E ≤ F) :
    ∃! c : pbcAmbientCompleteLocalization l Ω W E ⋙
        pbcAmbientCompleteRawTransition l Ω W h ≅
      pbcAmbientCompleteIntegralTransition l Ω W h ⋙
        pbcAmbientCompleteLocalization l Ω W F,
      (E = F → HEq c
        ((Functor.rightUnitor (pbcAmbientCompleteLocalization l Ω W E)) ≪≫
          (Functor.leftUnitor (pbcAmbientCompleteLocalization l Ω W E)).symm ≪≫
          Functor.isoWhiskerRight (pbcAmbientCompleteIntegralUnit l Ω W E).symm
            (pbcAmbientCompleteLocalization l Ω W E))) ∧
      (E ≠ F → HEq c
        (eqToIso (pbcAmbientCompleteRaw_exists l Ω W h).exists.choose_spec)) := by
  by_cases hEF : E = F
  · subst F
    rw [pbcAmbientCompleteRawTransition_refl l Ω W h]
    refine ⟨(Functor.rightUnitor (pbcAmbientCompleteLocalization l Ω W E)) ≪≫
      (Functor.leftUnitor (pbcAmbientCompleteLocalization l Ω W E)).symm ≪≫
      Functor.isoWhiskerRight (pbcAmbientCompleteIntegralUnit l Ω W E).symm
        (pbcAmbientCompleteLocalization l Ω W E),
      ⟨fun _ ↦ HEq.rfl, fun hne ↦ (hne rfl).elim⟩, ?_⟩
    intro e' he'
    exact eq_of_heq (he'.1 rfl)
  · rw [pbcAmbientCompleteRawTransition_of_ne l Ω W h hEF]
    refine ⟨eqToIso (pbcAmbientCompleteRaw_exists l Ω W h).exists.choose_spec,
      ⟨fun heq ↦ (hEF heq).elim, fun _ ↦ HEq.rfl⟩, ?_⟩
    intro e' he'
    exact eq_of_heq (he'.2 hEF)

/-- The uniquely normalized integral/rational tensor comparison.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
@[irreducible] def pbcAmbientCompleteIntegralComparison (h : E ≤ F) :=
  (pbcAmbientCompleteIntegralComparison_exists l Ω W h).exists.choose

/-- Restriction of the specified balanced ambient associator to complete objects.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system).
Proof: both complete subcategories are full. Lift the balanced tensor comparison
and its inverse. Faithfulness proves the naturality, inverse equations and uniqueness. -/
theorem pbcAmbientCompleteIntegralAssociator_exists (h : E ≤ F) (k : F ≤ G) :
    ∃! a : pbcAmbientCompleteIntegralTransition l Ω W h ⋙
        pbcAmbientCompleteIntegralTransition l Ω W k ≅
      pbcAmbientCompleteIntegralTransition l Ω W (h.trans k),
      HEq (Functor.whiskerRight a.hom
          (ObjectProperty.ι (WeilConjectures.IsPbcComplete l (pbcFiniteField.{u} l Ω G) W)))
        (Functor.whiskerLeft
          (ObjectProperty.ι (WeilConjectures.IsPbcComplete l (pbcFiniteField.{u} l Ω E) W))
          (pbcAmbientScalarAssociator l Ω W h k).hom) := by
  let a : pbcAmbientCompleteIntegralTransition l Ω W h ⋙
      pbcAmbientCompleteIntegralTransition l Ω W k ≅
      pbcAmbientCompleteIntegralTransition l Ω W (h.trans k) :=
    NatIso.ofComponents
      (fun K ↦ ObjectProperty.isoMk _ ((pbcAmbientScalarAssociator l Ω W h k).app K.obj))
      (fun f ↦ by
        apply ObjectProperty.hom_ext
        exact (pbcAmbientScalarAssociator l Ω W h k).hom.naturality f.hom)
  refine ⟨a, HEq.rfl, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact congrArg (fun η ↦ η.app K) (eq_of_heq ha')

/-- Complete integral tensor balancing, with its ambient normalization.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
@[irreducible] def pbcAmbientCompleteIntegralAssociator (h : E ≤ F) (k : F ≤ G) :=
  (pbcAmbientCompleteIntegralAssociator_exists l Ω W h k).exists.choose

/-- Rational associators are fixed by the integral balanced components.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system).
Proof: localize the integral associator and conjugate by the integral/rational
comparisons. Naturality holds on integral arrows and hence on their fractions.
Every raw object is integral, so the formula also gives uniqueness. -/
theorem pbcAmbientCompleteRawAssociator_exists (h : E ≤ F) (k : F ≤ G) :
    ∃! a : pbcAmbientCompleteRawTransition l Ω W h ⋙
        pbcAmbientCompleteRawTransition l Ω W k ≅
      pbcAmbientCompleteRawTransition l Ω W (h.trans k),
      ∀ K : WeilConjectures.PbcComplete l (pbcFiniteField.{u} l Ω E) W,
        a.hom.app ((pbcAmbientCompleteLocalization l Ω W E).obj K) =
          (pbcAmbientCompleteRawTransition l Ω W k).map
              ((pbcAmbientCompleteIntegralComparison l Ω W h).hom.app K) ≫
            (pbcAmbientCompleteIntegralComparison l Ω W k).hom.app
              ((pbcAmbientCompleteIntegralTransition l Ω W h).obj K) ≫
            (pbcAmbientCompleteLocalization l Ω W G).map
              ((pbcAmbientCompleteIntegralAssociator l Ω W h k).hom.app K) ≫
            (pbcAmbientCompleteIntegralComparison l Ω W (h.trans k)).inv.app K := by
  let Q := pbcAmbientCompleteLocalization l Ω W E
  let Bh := pbcAmbientCompleteRawTransition l Ω W h
  let Bk := pbcAmbientCompleteRawTransition l Ω W k
  let Bhk := pbcAmbientCompleteRawTransition l Ω W (h.trans k)
  let Ih := pbcAmbientCompleteIntegralTransition l Ω W h
  let Ik := pbcAmbientCompleteIntegralTransition l Ω W k
  let QF := pbcAmbientCompleteLocalization l Ω W F
  let QG := pbcAmbientCompleteLocalization l Ω W G
  let c : Q ⋙ (Bh ⋙ Bk) ≅ Q ⋙ Bhk :=
    (Functor.associator Q Bh Bk).symm ≪≫
      Functor.isoWhiskerRight (pbcAmbientCompleteIntegralComparison l Ω W h) Bk ≪≫
      Functor.associator Ih QF Bk ≪≫
      Functor.isoWhiskerLeft Ih (pbcAmbientCompleteIntegralComparison l Ω W k) ≪≫
      (Functor.associator Ih Ik QG).symm ≪≫
      Functor.isoWhiskerRight (pbcAmbientCompleteIntegralAssociator l Ω W h k) QG ≪≫
      (pbcAmbientCompleteIntegralComparison l Ω W (h.trans k)).symm
  let e : Bh ⋙ Bk ≅ Bhk := ScalarLocalization.liftNatIso (Bh ⋙ Bk) Bhk c
  have he (K : WeilConjectures.PbcComplete l (pbcFiniteField.{u} l Ω E) W) :
      c.hom.app K =
        Bk.map ((pbcAmbientCompleteIntegralComparison l Ω W h).hom.app K) ≫
        (pbcAmbientCompleteIntegralComparison l Ω W k).hom.app (Ih.obj K) ≫
        QG.map ((pbcAmbientCompleteIntegralAssociator l Ω W h k).hom.app K) ≫
        (pbcAmbientCompleteIntegralComparison l Ω W (h.trans k)).inv.app K :=
    (Category.id_comp _).trans (congrArg (_ ≫ ·) ((Category.id_comp _).trans
      (congrArg (_ ≫ ·) (Category.id_comp _))))
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact (he' K.obj).trans (he K.obj).symm

/-- The canonical rational tensor associator.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
@[irreducible] def pbcAmbientCompleteRawAssociator (h : E ≤ F) (k : F ≤ G) :=
  (pbcAmbientCompleteRawAssociator_exists l Ω W h k).exists.choose

private theorem pbcAmbientCompleteIntegralAssociator_hom (h : E ≤ F) (k : F ≤ G)
    (K : WeilConjectures.PbcComplete l (pbcFiniteField.{u} l Ω E) W) :
    ((pbcAmbientCompleteIntegralAssociator l Ω W h k).hom.app K).hom =
      (pbcAmbientScalarAssociator l Ω W h k).hom.app K.obj := by
  unfold pbcAmbientCompleteIntegralAssociator
  exact congrArg (fun η ↦ η.app K)
    (eq_of_heq (pbcAmbientCompleteIntegralAssociator_exists l Ω W h k).exists.choose_spec)

private theorem pbcAmbientCompleteIntegralUnit_hom (E : Padic.FiniteCoefficientFields l Ω)
    (K : WeilConjectures.PbcComplete l (pbcFiniteField.{u} l Ω E) W) :
    ((pbcAmbientCompleteIntegralUnit l Ω W E).hom.app K).hom =
      (pbcAmbientScalarUnit l Ω W E).hom.app K.obj := by
  unfold pbcAmbientCompleteIntegralUnit
  exact congrArg (fun η ↦ η.app K)
    (eq_of_heq (pbcAmbientCompleteIntegralUnit_exists l Ω W E).exists.choose_spec)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcAmbientCompleteIntegralAssociator_leftUnit (h : E ≤ F)
    (K : WeilConjectures.PbcComplete l (pbcFiniteField.{u} l Ω E) W) :
    (pbcAmbientCompleteIntegralAssociator l Ω W (le_refl E) h).hom.app K =
      (pbcAmbientCompleteIntegralTransition l Ω W h).map
        ((pbcAmbientCompleteIntegralUnit l Ω W E).hom.app K) := by
  apply ObjectProperty.hom_ext
  change _ = (pbcAmbientScalarExtension l Ω W h).map
    (((pbcAmbientCompleteIntegralUnit l Ω W E).hom.app K).hom)
  erw [pbcAmbientCompleteIntegralAssociator_hom, pbcAmbientCompleteIntegralUnit_hom]
  exact pbcAmbientAssociator_leftUnit l Ω W h K.obj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcAmbientCompleteIntegralAssociator_rightUnit (h : E ≤ F)
    (K : WeilConjectures.PbcComplete l (pbcFiniteField.{u} l Ω E) W) :
    (pbcAmbientCompleteIntegralAssociator l Ω W h (le_refl F)).hom.app K =
      (pbcAmbientCompleteIntegralUnit l Ω W F).hom.app
        ((pbcAmbientCompleteIntegralTransition l Ω W h).obj K) := by
  apply ObjectProperty.hom_ext
  erw [pbcAmbientCompleteIntegralAssociator_hom, pbcAmbientCompleteIntegralUnit_hom]
  exact pbcAmbientAssociator_rightUnit l Ω W h K.obj

private theorem pbcAmbientCompleteIntegralAssociator_cocycle
    {H : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) (k : F ≤ G) (j : G ≤ H)
    (K : WeilConjectures.PbcComplete l (pbcFiniteField.{u} l Ω E) W) :
    (pbcAmbientCompleteIntegralTransition l Ω W j).map
        ((pbcAmbientCompleteIntegralAssociator l Ω W h k).hom.app K) ≫
      (pbcAmbientCompleteIntegralAssociator l Ω W (h.trans k) j).hom.app K =
    (pbcAmbientCompleteIntegralAssociator l Ω W k j).hom.app
        ((pbcAmbientCompleteIntegralTransition l Ω W h).obj K) ≫
      (pbcAmbientCompleteIntegralAssociator l Ω W h (k.trans j)).hom.app K := by
  apply ObjectProperty.hom_ext
  change (pbcAmbientScalarExtension l Ω W j).map
      (((pbcAmbientCompleteIntegralAssociator l Ω W h k).hom.app K).hom) ≫ _ = _
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    pbcAmbientCompleteIntegralAssociator_hom]
  exact pbcAmbientScalarAssociator_cocycle l Ω W h k j K.obj

private theorem pbcAmbientCompleteIntegralComparison_refl
    (E : Padic.FiniteCoefficientFields l Ω)
    (hs : pbcAmbientCompleteRawTransition l Ω W (le_refl E) = 𝟭 _) :
    pbcAmbientCompleteIntegralComparison l Ω W (le_refl E) =
      eqToIso (congrArg (fun B ↦ pbcAmbientCompleteLocalization l Ω W E ⋙ B) hs) ≪≫
        (Functor.rightUnitor (pbcAmbientCompleteLocalization l Ω W E) ≪≫
          (Functor.leftUnitor (pbcAmbientCompleteLocalization l Ω W E)).symm ≪≫
          Functor.isoWhiskerRight (pbcAmbientCompleteIntegralUnit l Ω W E).symm
            (pbcAmbientCompleteLocalization l Ω W E)) := by
  unfold pbcAmbientCompleteIntegralComparison
  apply eq_of_heq
  exact ((pbcAmbientCompleteIntegralComparison_exists l Ω W (le_refl E)).exists.choose_spec.1
    rfl).trans (pbcTransportIso_heq
      (congrArg (fun B ↦ pbcAmbientCompleteLocalization l Ω W E ⋙ B) hs) _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcAmbientCompleteRawAssociator_normalization (h : E ≤ F) (k : F ≤ G)
    (K : WeilConjectures.PbcComplete l (pbcFiniteField.{u} l Ω E) W) :
    (pbcAmbientCompleteRawAssociator l Ω W h k).hom.app
        ((pbcAmbientCompleteLocalization l Ω W E).obj K) ≫
      (pbcAmbientCompleteIntegralComparison l Ω W (h.trans k)).hom.app K =
    (pbcAmbientCompleteRawTransition l Ω W k).map
        ((pbcAmbientCompleteIntegralComparison l Ω W h).hom.app K) ≫
      (pbcAmbientCompleteIntegralComparison l Ω W k).hom.app
        ((pbcAmbientCompleteIntegralTransition l Ω W h).obj K) ≫
      (pbcAmbientCompleteLocalization l Ω W G).map
        ((pbcAmbientCompleteIntegralAssociator l Ω W h k).hom.app K) := by
  unfold pbcAmbientCompleteRawAssociator
  rw [(pbcAmbientCompleteRawAssociator_exists l Ω W h k).exists.choose_spec K]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcAmbientCompleteRawAssociator_leftUnit (h : E ≤ F)
    (hs : pbcAmbientCompleteRawTransition l Ω W (le_refl E) = 𝟭 _) :
    pbcAmbientCompleteRawAssociator l Ω W (le_refl E) h =
      eqToIso (congrArg (fun B ↦ B ⋙ pbcAmbientCompleteRawTransition l Ω W h) hs) ≪≫
        Functor.leftUnitor (pbcAmbientCompleteRawTransition l Ω W h) := by
  unfold pbcAmbientCompleteRawAssociator
  symm
  apply (pbcAmbientCompleteRawAssociator_exists l Ω W (le_refl E) h).unique _
    (pbcAmbientCompleteRawAssociator_exists l Ω W (le_refl E) h).exists.choose_spec
  intro K
  apply (cancel_mono ((pbcAmbientCompleteIntegralComparison l Ω W h).hom.app K)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [pbcAmbientCompleteIntegralAssociator_leftUnit,
    pbcAmbientCompleteIntegralComparison_refl l Ω W E hs]
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, NatTrans.comp_app,
    eqToHom_app, Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp,
    Functor.leftUnitor_hom_app]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := (pbcAmbientCompleteIntegralComparison l Ω W h).hom.naturality
    ((pbcAmbientCompleteIntegralUnit l Ω W E).inv.app K)
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp, Category.comp_id]
  have hu := congrArg (fun f ↦ (pbcAmbientCompleteLocalization l Ω W F).map
    ((pbcAmbientCompleteIntegralTransition l Ω W h).map f))
    (Iso.inv_hom_id_app (pbcAmbientCompleteIntegralUnit l Ω W E) K)
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at hu
  erw [hu]
  erw [Category.comp_id]
  simp only [eqToHom_map]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcAmbientCompleteRawAssociator_rightUnit (h : E ≤ F)
    (hs : pbcAmbientCompleteRawTransition l Ω W (le_refl F) = 𝟭 _) :
    pbcAmbientCompleteRawAssociator l Ω W h (le_refl F) =
      eqToIso (congrArg (fun B ↦ pbcAmbientCompleteRawTransition l Ω W h ⋙ B) hs) ≪≫
        Functor.rightUnitor (pbcAmbientCompleteRawTransition l Ω W h) := by
  unfold pbcAmbientCompleteRawAssociator
  symm
  apply (pbcAmbientCompleteRawAssociator_exists l Ω W h (le_refl F)).unique _
    (pbcAmbientCompleteRawAssociator_exists l Ω W h (le_refl F)).exists.choose_spec
  intro K
  apply (cancel_mono ((pbcAmbientCompleteIntegralComparison l Ω W h).hom.app K)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [pbcAmbientCompleteIntegralAssociator_rightUnit,
    pbcAmbientCompleteIntegralComparison_refl l Ω W F hs]
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, NatTrans.comp_app,
    eqToHom_app, Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp,
    Category.assoc]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  erw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]
  have hn := (eqToIso hs).hom.naturality
    ((pbcAmbientCompleteIntegralComparison l Ω W h).hom.app K)
  simpa only [eqToIso.hom, eqToHom_app, Functor.id_map] using hn.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcAmbientCompleteRawAssociator_cocycle
    {H : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) (k : F ≤ G) (j : G ≤ H)
    (K : pbcAmbientCompleteStage l Ω W E) :
    (pbcAmbientCompleteRawTransition l Ω W j).map
          ((pbcAmbientCompleteRawAssociator l Ω W h k).hom.app K) ≫
        (pbcAmbientCompleteRawAssociator l Ω W (h.trans k) j).hom.app K =
      (pbcAmbientCompleteRawAssociator l Ω W k j).hom.app
          ((pbcAmbientCompleteRawTransition l Ω W h).obj K) ≫
        (pbcAmbientCompleteRawAssociator l Ω W h (k.trans j)).hom.app K := by
  obtain ⟨KE⟩ := K
  let Ih := pbcAmbientCompleteIntegralTransition l Ω W h
  let Ik := pbcAmbientCompleteIntegralTransition l Ω W k
  let Bj := pbcAmbientCompleteRawTransition l Ω W j
  let Bk := pbcAmbientCompleteRawTransition l Ω W k
  let QH := pbcAmbientCompleteLocalization l Ω W H
  have hn := (pbcAmbientCompleteRawAssociator l Ω W k j).hom.naturality
    ((pbcAmbientCompleteIntegralComparison l Ω W h).hom.app KE)
  have hc := (pbcAmbientCompleteIntegralComparison l Ω W j).hom.naturality
    ((pbcAmbientCompleteIntegralAssociator l Ω W h k).hom.app KE)
  apply (cancel_mono
    ((pbcAmbientCompleteIntegralComparison l Ω W (h.trans (k.trans j))).hom.app KE)).1
  simp only [Category.assoc]
  erw [pbcAmbientCompleteRawAssociator_normalization l Ω W (h.trans k) j KE,
    pbcAmbientCompleteRawAssociator_normalization l Ω W h (k.trans j) KE]
  rw [← CategoryTheory.Functor.map_comp_assoc]
  erw [pbcAmbientCompleteRawAssociator_normalization l Ω W h k KE]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  simp only [Functor.comp_map] at hn hc
  erw [← reassoc_of% hn]
  erw [reassoc_of% hc]
  erw [reassoc_of% (pbcAmbientCompleteRawAssociator_normalization l Ω W k j (Ih.obj KE))]
  have hh := congrArg (fun f ↦ QH.map f)
    (pbcAmbientCompleteIntegralAssociator_cocycle l Ω W h k j KE)
  simp only [CategoryTheory.Functor.map_comp] at hh
  exact congrArg (fun f ↦
    Bj.map (Bk.map ((pbcAmbientCompleteIntegralComparison l Ω W h).hom.app KE)) ≫
      Bj.map ((pbcAmbientCompleteIntegralComparison l Ω W k).hom.app (Ih.obj KE)) ≫
      (pbcAmbientCompleteIntegralComparison l Ω W j).hom.app (Ik.obj (Ih.obj KE)) ≫ f) hh

/-- The canonical raw system has additive transitions, normalized units and tensor pentagon.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system).
Proof: finite tensor and localization preserve addition. The equal-field branch
is identity. The section-normalized tensor unit satisfies the unit equations
with balancing. The two tensor-balancing composites agree on pure tensors.
Their derived, full-subcategory and localized images give the displayed pentagon. -/
theorem pbcAmbientCompleteRaw_laws (h : E ≤ F) (k : F ≤ G)
    {H : Padic.FiniteCoefficientFields l Ω} (j : G ≤ H) :
    (pbcAmbientCompleteRawTransition l Ω W h).Additive ∧
    pbcAmbientCompleteRawTransition l Ω W (le_refl E) = 𝟭 _ ∧
    HEq (pbcAmbientCompleteRawAssociator l Ω W (le_refl E) h)
      (Functor.leftUnitor (pbcAmbientCompleteRawTransition l Ω W h)) ∧
    HEq (pbcAmbientCompleteRawAssociator l Ω W h (le_refl F))
      (Functor.rightUnitor (pbcAmbientCompleteRawTransition l Ω W h)) ∧
    (∀ K : pbcAmbientCompleteStage l Ω W E,
      (pbcAmbientCompleteRawTransition l Ω W j).map
          ((pbcAmbientCompleteRawAssociator l Ω W h k).hom.app K) ≫
        (pbcAmbientCompleteRawAssociator l Ω W (h.trans k) j).hom.app K =
      (pbcAmbientCompleteRawAssociator l Ω W k j).hom.app
          ((pbcAmbientCompleteRawTransition l Ω W h).obj K) ≫
        (pbcAmbientCompleteRawAssociator l Ω W h (k.trans j)).hom.app K) := by
  have hsE := pbcAmbientCompleteRawTransition_refl l Ω W (le_refl E)
  have hsF := pbcAmbientCompleteRawTransition_refl l Ω W (le_refl F)
  refine ⟨?_, hsE, ?_, ?_, pbcAmbientCompleteRawAssociator_cocycle l Ω W h k j⟩
  · by_cases hEF : E = F
    · subst F
      rw [pbcAmbientCompleteRawTransition_refl l Ω W h]
      infer_instance
    · rw [pbcAmbientCompleteRawTransition_of_ne l Ω W h hEF,
        (pbcAmbientCompleteRaw_exists l Ω W h).unique
          (pbcAmbientCompleteRaw_exists l Ω W h).exists.choose_spec
          (pbcAmbientCompleteRawExtension_spec l Ω W h)]
      exact pbcAmbientCompleteRawExtension_additive l Ω W h
  · exact (heq_of_eq (pbcAmbientCompleteRawAssociator_leftUnit l Ω W h hsE)).trans
      (pbcTransportIso_heq
        (congrArg (fun B ↦ B ⋙ pbcAmbientCompleteRawTransition l Ω W h) hsE) _)
  · exact (heq_of_eq (pbcAmbientCompleteRawAssociator_rightUnit l Ω W h hsF)).trans
      (pbcTransportIso_heq
        (congrArg (fun B ↦ pbcAmbientCompleteRawTransition l Ω W h ⋙ B) hsF) _)

end Construction

/-- The actual ambient raw scalar-extension system, rather than an arbitrary diagram.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
def pbcAmbientCompleteRawSystem :
    StageSystem (fun E : Padic.FiniteCoefficientFields l Ω ↦ pbcAmbientCompleteStage l Ω W E)
    where
  T h := pbcAmbientCompleteRawTransition l Ω W h
  assoc h k := pbcAmbientCompleteRawAssociator l Ω W h k
  cocycle h k j K := (pbcAmbientCompleteRaw_laws l Ω W h k j).2.2.2.2 K

end AlgebraicGeometry.Scheme
