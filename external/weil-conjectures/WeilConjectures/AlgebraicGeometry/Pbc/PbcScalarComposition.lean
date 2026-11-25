/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor

/-! # Units and composition of finite coefficient extension

Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.

## References

* Milne, Section 19
* Stacks 03DA
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime]
variable (E F G : Type u) [Field E] [Field F] [Field G]
variable [Algebra (Padic l) E] [Algebra (Padic l) F] [Algebra (Padic l) G]
variable [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
variable [FiniteDimensional (Padic l) G]
variable (i : E →ₐ[Padic l] F) (j : F →ₐ[Padic l] G) (T : Scheme.{u})

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Completed coefficient maps compose as the actual field embeddings do. -/
theorem pbcScalarCoefficientMap_comp :
    pbcScalarCoefficientMap l E F i T ≫ pbcScalarCoefficientMap l F G j T =
      pbcScalarCoefficientMap l E G (j.comp i) T := by
  have hEF := (pbcScalarCoefficientMap_exists l E F i T).exists.choose_spec
  have hFG := (pbcScalarCoefficientMap_exists l F G j T).exists.choose_spec
  have hEG := (pbcScalarCoefficientMap_exists l E G (j.comp i) T).exists.choose_spec
  apply limit.hom_ext
  intro n
  change (pbcScalarCoefficientMap l E F i T ≫ pbcScalarCoefficientMap l F G j T) ≫
      pbcAdicProjection T (pbcIntegralDatum l G) n.unop =
    pbcScalarCoefficientMap l E G (j.comp i) T ≫
      pbcAdicProjection T (pbcIntegralDatum l G) n.unop
  dsimp only [pbcScalarCoefficientMap]
  rw [Category.assoc, hFG, ← Category.assoc, hEF, Category.assoc, hEG,
    pbcFiniteCoefficientMap_comp]
  congr 2
  ext x
  induction x using Quotient.inductionOn' with
  | h x => rfl

/-- The canonical balancing components are natural on derived objects. -/
theorem pbcAmbientScalarComp_naturality
    (K L : PbcCompletedDerived T (pbcIntegralDatum l E)) (f : K ⟶ L) :
    (pbcEmbeddingAmbientTensor l F G j T).map
        ((pbcEmbeddingAmbientTensor l E F i T).map f) ≫
      (pbcReductionNormalization (pbcScalarCoefficientMap l E F i T)
        (pbcScalarCoefficientMap l F G j T) (pbcScalarCoefficientMap l E G (j.comp i) T)
        (pbcScalarCoefficientMap_comp l E F G i j T) L).hom =
    (pbcReductionNormalization (pbcScalarCoefficientMap l E F i T)
        (pbcScalarCoefficientMap l F G j T) (pbcScalarCoefficientMap l E G (j.comp i) T)
        (pbcScalarCoefficientMap_comp l E F G i j T) K).hom ≫
      (pbcEmbeddingAmbientTensor l E G (j.comp i) T).map f := by
  let φ := pbcScalarCoefficientMap l E F i T
  let ψ := pbcScalarCoefficientMap l F G j T
  let χ := pbcScalarCoefficientMap l E G (j.comp i) T
  let h := pbcScalarCoefficientMap_comp l E F G i j T
  let e := Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction φ)
    (pbcDerivedScalarAdjunction ψ) (pbcDerivedScalarAdjunction χ)
    (pbcDerivedRestrictComp φ ψ χ h)
  have he (M : PbcCompletedDerived T (pbcIntegralDatum l E)) :
      (pbcReductionNormalization φ ψ χ h M).hom = e.hom.app M := by
    dsimp [pbcReductionNormalization, pbcReductionNormalizationHom,
      pbcReductionTransition, e]
    simp only [asIso_hom, Adjunction.leftAdjointCompIso_hom_app,
      Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [he, he]
  exact e.hom.naturality f

/-- The ambient associator is the adjunction-normalized balanced tensor comparison. -/
@[irreducible] def pbcAmbientScalarComp :
    pbcEmbeddingAmbientTensor l E F i T ⋙ pbcEmbeddingAmbientTensor l F G j T ≅
      pbcEmbeddingAmbientTensor l E G (j.comp i) T :=
  NatIso.ofComponents
    (pbcReductionNormalization (pbcScalarCoefficientMap l E F i T)
      (pbcScalarCoefficientMap l F G j T) (pbcScalarCoefficientMap l E G (j.comp i) T)
      (pbcScalarCoefficientMap_comp l E F G i j T))
    (fun f ↦ pbcAmbientScalarComp_naturality l E F G i j T _ _ f)

variable [IsNoetherian T] (hDim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
variable (hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

/-- Rational balancing is the image of the specified ambient balanced comparison. -/
@[irreducible]
def pbcRationalScalarCompComponent (K : PbcRationalDerivedCategory l E T hDim hInv) :
    (pbcRationalScalarExtension l F G j T hDim hInv).obj
        ((pbcRationalScalarExtension l E F i T hDim hInv).obj K) ≅
      (pbcRationalScalarExtension l E G (j.comp i) T hDim hInv).obj K :=
  (pbcRationalization T (pbcIntegralDatum l G) (pbcUniformizer l G)).mapIso
    (ObjectProperty.isoMk (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l G))
      ((pbcAmbientScalarComp l E F G i j T).app K.obj.obj))

section
attribute [-instance] ULift.module
attribute [local irreducible] pbcRationalScalarHom
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual localized balancing components are natural on all rational morphisms. -/
theorem pbcRationalScalarComp_naturality
    (K L : PbcRationalDerivedCategory l E T hDim hInv) (f : K ⟶ L) :
    (pbcRationalScalarExtension l F G j T hDim hInv).map
        ((pbcRationalScalarExtension l E F i T hDim hInv).map f) ≫
      (pbcRationalScalarCompComponent l E F G i j T hDim hInv L).hom =
    (pbcRationalScalarCompComponent l E F G i j T hDim hInv K).hom ≫
      (pbcRationalScalarExtension l E G (j.comp i) T hDim hInv).map f := by
  let I := pbcEmbeddingIntegralTensor l E F i T hDim hInv
  let J := pbcEmbeddingIntegralTensor l F G j T hDim hInv
  let D := pbcEmbeddingIntegralTensor l E G (j.comp i) T hDim hInv
  let Q := pbcRationalization T (pbcIntegralDatum l G) (pbcUniformizer l G)
  let η (M : PbcIntegralCategory l E T hDim hInv) : J.obj (I.obj M) ⟶ D.obj M :=
    ObjectProperty.homMk ((pbcAmbientScalarComp l E F G i j T).hom.app M.obj)
  have hn (f : K.obj ⟶ L.obj) : J.map (I.map f) ≫ η L.obj = η K.obj ≫ D.map f := by
    apply ObjectProperty.hom_ext
    exact (pbcAmbientScalarComp l E F G i j T).hom.naturality f.hom
  unfold pbcRationalScalarCompComponent
  dsimp only [pbcRationalScalarExtension]
  change pbcRationalScalarHom l F G j T hDim hInv (I.obj K.obj) (I.obj L.obj)
      (pbcRationalScalarHom l E F i T hDim hInv K.obj L.obj f) ≫ Q.map (η L.obj) =
    Q.map (η K.obj) ≫ pbcRationalScalarHom l E G (j.comp i) T hDim hInv K.obj L.obj f
  induction f using TensorProduct.inductionOn with
  | tmul a f =>
    rw [pbcRationalScalarHom_tmul, pbcRationalScalarHom_tmul, pbcRationalScalarHom_tmul]
    change ScalarLocalization.composition _ _ _ _ _ _
        ((1 : Localization.Away (pbcUniformizer l G)) ⊗ₜ[PbcIntegralRing l G] η L.obj)
        (_ ⊗ₜ[PbcIntegralRing l G] J.map (I.map f)) =
      ScalarLocalization.composition _ _ _ _ _ _
        (_ ⊗ₜ[PbcIntegralRing l G] D.map f)
        ((1 : Localization.Away (pbcUniformizer l G)) ⊗ₜ[PbcIntegralRing l G] η K.obj)
    rw [ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul]
    simp only [RingEquiv.apply_symm_apply, AlgHom.comp_apply, one_mul, mul_one]
    exact congrArg (fun z ↦
      (pbcRationalCoefficientEquiv l G).symm (j (i (pbcRationalCoefficientEquiv l E a)))
        ⊗ₜ[PbcIntegralRing l G] z) (hn f)
  | add f g hf hg =>
    simp only [_root_.map_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
end

/-- The specified natural rational associator before literal-unit normalization. -/
@[irreducible] def pbcRationalScalarComp :
    pbcRationalScalarExtension l E F i T hDim hInv ⋙
        pbcRationalScalarExtension l F G j T hDim hInv ≅
      pbcRationalScalarExtension l E G (j.comp i) T hDim hInv :=
  NatIso.ofComponents (pbcRationalScalarCompComponent l E F G i j T hDim hInv)
    (fun f ↦ pbcRationalScalarComp_naturality l E F G i j T hDim hInv _ _ f)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
section Units
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
variable [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Identity scalar restriction is fixed by identity functions on sections. -/
theorem pbcScalarRestrictId_exists :
    ∃! e : pbcRestrict (𝟙 (pbcAdicCompletion T (pbcIntegralDatum l E))) ≅ 𝟭 _,
      ∀ (M : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))
        (U : T.ProEtᵒᵖ) (x : M.val.obj U), (e.hom.app M).val.app U x = x := by
  let R := pbcAdicCompletion T (pbcIntegralDatum l E)
  let eM (M : pbcModules T R) : (pbcRestrict (𝟙 R)).obj M ≅ M :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        ModuleCat.restrictScalarsId'App _ rfl (M.val.obj U))
        (fun {U V} f ↦ by ext x; rfl))
  let e : pbcRestrict (𝟙 R) ≅ 𝟭 _ :=
    NatIso.ofComponents eM (fun f ↦ by ext U x; rfl)
  refine ⟨e, ?_, ?_⟩
  · intro M U x
    rfl
  · intro e' he'
    apply Iso.ext
    ext M U x
    exact he' M U x

/-- The ordinary identity-on-sections restriction comparison. -/
@[irreducible] def pbcScalarRestrictId := (pbcScalarRestrictId_exists l E T).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The identity completed coefficient map fixes all finite projections. -/
theorem pbcScalarCoefficientMap_id :
    pbcScalarCoefficientMap l E E (AlgHom.id (Padic l) E) T =
      𝟙 (pbcAdicCompletion T (pbcIntegralDatum l E)) := by
  have h := (pbcScalarCoefficientMap_exists l E E (AlgHom.id (Padic l) E) T
    ).exists.choose_spec
  apply limit.hom_ext
  intro n
  change pbcScalarCoefficientMap l E E (AlgHom.id (Padic l) E) T ≫
    pbcAdicProjection T (pbcIntegralDatum l E) n.unop = _
  dsimp only [pbcScalarCoefficientMap]
  rw [h, Category.id_comp]
  have he : pbcScalarQuotientMap l E E (AlgHom.id (Padic l) E) n.unop =
      RingHom.id _ := by
    ext x
    induction x using Quotient.inductionOn' with
    | h x => rfl
  rw [he, pbcFiniteCoefficientMap_id]
  exact Category.comp_id _

/-- The canonical tensor unit is conjugate to identity restriction under the
ordinary-unit-normalized derived adjunction. -/
@[irreducible] def pbcEmbeddingAmbientUnit :
    pbcEmbeddingAmbientTensor l E E (AlgHom.id (Padic l) E) T ≅ 𝟭 _ :=
  eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ) (pbcScalarCoefficientMap_id l E T)) ≪≫
    ((conjugateIsoEquiv
      (pbcDerivedScalarAdjunction (𝟙 (pbcAdicCompletion T (pbcIntegralDatum l E))))
      (Adjunction.id : (𝟭 (PbcCompletedDerived T (pbcIntegralDatum l E))) ⊣ 𝟭 _)).symm
        (Functor.mapDerivedCategoryNatIso (pbcScalarRestrictId l E T) ≪≫
          Functor.mapDerivedCategoryIdIso _)).symm

variable [IsNoetherian T]
variable (hDim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
variable (hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

/-- Rational tensor unit components are localizations of the ambient tensor units. -/
@[irreducible]
def pbcRationalScalarUnitComponent (K : PbcRationalDerivedCategory l E T hDim hInv) :
    (pbcRationalScalarExtension l E E (AlgHom.id (Padic l) E) T hDim hInv).obj K ≅ K :=
  (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).mapIso
    (ObjectProperty.isoMk (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))
      ((pbcEmbeddingAmbientUnit l E T).app K.obj.obj))

section
attribute [-instance] ULift.module
attribute [local irreducible] pbcRationalScalarHom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified unit components are natural on every localized Hom module. -/
theorem pbcRationalScalarUnit_naturality
    (K L : PbcRationalDerivedCategory l E T hDim hInv) (f : K ⟶ L) :
    (pbcRationalScalarExtension l E E (AlgHom.id (Padic l) E) T hDim hInv).map f ≫
        (pbcRationalScalarUnitComponent l E T hDim hInv L).hom =
      (pbcRationalScalarUnitComponent l E T hDim hInv K).hom ≫ f := by
  let I := pbcEmbeddingIntegralTensor l E E (AlgHom.id (Padic l) E) T hDim hInv
  let Q := pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)
  let η (M : PbcIntegralCategory l E T hDim hInv) : I.obj M ⟶ M :=
    ObjectProperty.homMk ((pbcEmbeddingAmbientUnit l E T).hom.app M.obj)
  have hn (f : K.obj ⟶ L.obj) : I.map f ≫ η L.obj = η K.obj ≫ f := by
    apply ObjectProperty.hom_ext
    exact (pbcEmbeddingAmbientUnit l E T).hom.naturality f.hom
  unfold pbcRationalScalarUnitComponent
  dsimp only [pbcRationalScalarExtension]
  change pbcRationalScalarHom l E E (AlgHom.id (Padic l) E) T hDim hInv
      K.obj L.obj f ≫ Q.map (η L.obj) = Q.map (η K.obj) ≫ f
  induction f using TensorProduct.inductionOn with
  | tmul a f =>
    rw [pbcRationalScalarHom_tmul]
    change ScalarLocalization.composition _ _ _ _ _ _
        ((1 : Localization.Away (pbcUniformizer l E)) ⊗ₜ[PbcIntegralRing l E] η L.obj)
        (_ ⊗ₜ[PbcIntegralRing l E] I.map f) =
      ScalarLocalization.composition _ _ _ _ _ _ (a ⊗ₜ[PbcIntegralRing l E] f)
        ((1 : Localization.Away (pbcUniformizer l E)) ⊗ₜ[PbcIntegralRing l E] η K.obj)
    rw [ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul]
    simp only [AlgHom.id_apply, RingEquiv.symm_apply_apply, one_mul, mul_one]
    exact congrArg (fun z ↦ a ⊗ₜ[PbcIntegralRing l E] z) (hn f)
  | add f g hf hg =>
    simp only [_root_.map_add, Preadditive.add_comp, hf, hg]
    exact (Preadditive.comp_add _ _ _ _ _ _).symm

end

/-- The natural rational tensor unit, before choosing literal identity transitions. -/
@[irreducible] def pbcRationalScalarUnit :
    pbcRationalScalarExtension l E E (AlgHom.id (Padic l) E) T hDim hInv ≅ 𝟭 _ :=
  NatIso.ofComponents (pbcRationalScalarUnitComponent l E T hDim hInv)
    (fun f ↦ pbcRationalScalarUnit_naturality l E T hDim hInv _ _ f)
end Units
end AlgebraicGeometry.Scheme
