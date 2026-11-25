/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IndEtaleMapping.IndEtaleDerivedImageHomCounit
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

/-! # Compatibility of the left-adjoint comparisons with composition

The comparison `imageTensorIso` of the left adjoints computing global Hom is compatible with
inverse-image composition, and restriction along a morphism `g` has the counit normalization
`restriction_counit`. These are the coherence inputs of `imageHomIso_naturality`.
Source: Stacks 08JA (blueprint: lem-per-ind-etale-derived-image-hom-adjunction).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale.IndEtaleMapping

variable (A : Type (u + 1)) [CommRing A]
variable {X : Scheme.{u}} (K M : DerivedCategoryModule A X)

/-- The pointwise form of `imageTensorIso`: the constant-pullback comparison followed by the
tensor constraint of inverse image. -/
theorem imageTensorIso_hom_app (K : DerivedCategoryModule A X) (T : Over X)
    (Q : DerivedCategory (ModuleCat.{u + 1} A)) :
    (imageTensorIso A K T).hom.app Q =
      ((ExternalRHom.pull A T.hom).obj K ◁
          (ExternalRHom.constantPullbackIso A T.hom).hom.app Q) ≫
        (ExternalRHom.pullTensorIso A T.hom K ((ExternalRHom.constant A X).obj Q)).hom := by
  simp only [imageTensorIso, ExternalRHom.pullTensorIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.comp_id, Category.id_comp, Functor.Monoidal.commTensorLeft_hom_app,
    Functor.Monoidal.μIso_hom, Functor.comp_obj, Iso.symm_hom, tensorLeft, curriedTensor]

/-- The comparison `imageTensorIso`, stated for a morphism `g` rather than an object of an
over category. The kernel can only identify `(Over.mk g).hom` with `g` below projections of
the derived functors by unfolding them, so `imageHomIso_naturality` is proved with `g`. -/
def restrictTensorIso {Y P : Scheme.{u}} (g : P ⟶ Y) (K : DerivedCategoryModule A Y) :
    ExternalRHom.constant A P ⋙ tensorLeft ((ExternalRHom.pull A g).obj K) ≅
      (ExternalRHom.constant A Y ⋙ tensorLeft K) ⋙ ExternalRHom.pull A g := by
  letI := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} A) g
  exact Functor.isoWhiskerRight (ExternalRHom.constantPullbackIso A g) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.Monoidal.commTensorLeft (ExternalRHom.pull A g) K) ≪≫
    (Functor.associator _ _ _).symm

/-- The pointwise form of `restrictTensorIso`. -/
theorem restrictTensorIso_hom_app {Y P : Scheme.{u}} (g : P ⟶ Y)
    (K : DerivedCategoryModule A Y) (Q : DerivedCategory (ModuleCat.{u + 1} A)) :
    (restrictTensorIso A g K).hom.app Q =
      ((ExternalRHom.pull A g).obj K ◁
          (ExternalRHom.constantPullbackIso A g).hom.app Q) ≫
        (ExternalRHom.pullTensorIso A g K ((ExternalRHom.constant A Y).obj Q)).hom := by
  simp only [restrictTensorIso, ExternalRHom.pullTensorIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.comp_id, Category.id_comp, Functor.Monoidal.commTensorLeft_hom_app,
    Functor.Monoidal.μIso_hom, Functor.comp_obj, Iso.symm_hom, tensorLeft, curriedTensor]

/-- `imageRestriction_counit`, stated for a morphism `g` rather than an object of an over
category. -/
theorem restriction_counit {Y P : Scheme.{u}} (g : P ⟶ Y)
    (K M : DerivedCategoryModule A Y) :
    (ExternalRHom.constant A P ⋙ tensorLeft ((ExternalRHom.pull A g).obj K)).map
        (ExternalRHom.restriction A g K M) ≫
      (ExternalRHom.globalAdjunction A ((ExternalRHom.pull A g).obj K)).counit.app
        ((ExternalRHom.pull A g).obj M) =
      (restrictTensorIso A g K).hom.app
        (((ExternalRHom.globalHom A Y).obj (op K)).obj M) ≫
      (ExternalRHom.pull A g).map ((ExternalRHom.globalAdjunction A K).counit.app M) := by
  let := ExternalRHom.derivedBraiding A Y
  let := ExternalRHom.derivedBraiding A P
  let := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} A) g
  let Q := ((ExternalRHom.globalHom A Y).obj (op K)).obj M
  have hb := (leftDerivedUpperStar_μ_map_braiding_hom (ModuleCat.{u + 1} A)
    g K ((ExternalRHom.constant A Y).obj Q)).symm
  have h := pulledEvaluation_left (ExternalRHom.pull A g)
    (ExternalRHom.constant A Y) (ExternalRHom.constant A P)
    (ExternalRHom.constantPullbackIso A g) K M Q
    ((ExternalRHom.globalAdjunction A K).counit.app M) hb
  change ((ExternalRHom.globalAdjunction A
    ((ExternalRHom.pull A g).obj K)).homEquiv _ _).symm
      (ExternalRHom.restriction A g K M) = _
  rw [ExternalRHom.restriction, ExternalRHom.transpose, Equiv.symm_apply_apply]
  simpa only [ExternalRHom.pulledEvaluation, ExternalRHom.evaluation,
    restrictTensorIso, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
    Category.id_comp, Functor.Monoidal.commTensorLeft_hom_app,
    Functor.Monoidal.μIso_hom, Functor.comp_obj, Iso.symm_hom,
    ExternalRHom.pullTensorIso, Q, tensorLeft, curriedTensor, Category.assoc] using h

/-- The tensor constraint of inverse image is natural in its second variable. -/
@[reassoc]
theorem pullTensorIso_hom_natural_right {Y P : Scheme.{u}} (a : P ⟶ Y)
    (E : DerivedCategoryModule A Y) {H H' : DerivedCategoryModule A Y} (g : H ⟶ H') :
    ((ExternalRHom.pull A a).obj E ◁ (ExternalRHom.pull A a).map g) ≫
        (ExternalRHom.pullTensorIso A a E H').hom =
      (ExternalRHom.pullTensorIso A a E H).hom ≫ (ExternalRHom.pull A a).map (E ◁ g) := by
  let := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} A) a
  exact Functor.LaxMonoidal.μ_natural_right _ _ _

/-- The composition isomorphism of inverse images is compatible with the specified tensor
constraints. -/
theorem pullTensorIso_hom_comp {T' S' R' : Scheme.{u}} (g₁ : T' ⟶ S') (g₂ : S' ⟶ R')
    (g₁₂ : T' ⟶ R') (hg : g₁₂ = g₁ ≫ g₂) (E H : DerivedCategoryModule A R') :
    (ExternalRHom.pullTensorIso A g₁₂ E H).hom ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g₁ g₂ g₁₂ hg).hom.app (E ⊗ H) =
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g₁ g₂ g₁₂ hg).hom.app E ⊗ₘ
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g₁ g₂ g₁₂ hg).hom.app H) ≫
        (ExternalRHom.pullTensorIso A g₁ _ _).hom ≫
          (ExternalRHom.pull A g₁).map (ExternalRHom.pullTensorIso A g₂ E H).hom := by
  have h : (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g₁ g₂ g₁₂ hg).hom.app (E ⊗ H) ≫
      (ExternalRHom.pull A g₁).map (ExternalRHom.pullTensorIso A g₂ E H).inv ≫
        (ExternalRHom.pullTensorIso A g₁ _ _).inv =
      (ExternalRHom.pullTensorIso A g₁₂ E H).inv ≫
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g₁ g₂ g₁₂ hg).hom.app E ⊗ₘ
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g₁ g₂ g₁₂ hg).hom.app H) :=
    (leftDerivedUpperStarTensorComparison_comp (ModuleCat.{u + 1} A) g₁ g₂ g₁₂ hg E H).symm
  rw [← Iso.eq_inv_comp, ← reassoc_of% h]
  simp

/-- The constant-pullback comparison respects composition, for any specified composite. -/
theorem constantPullbackIso_hom_comp {T' S' R' : Scheme.{u}} (g₁ : T' ⟶ S') (g₂ : S' ⟶ R')
    (g₁₂ : T' ⟶ R') (hg : g₁₂ = g₁ ≫ g₂) (Z : DerivedCategory (ModuleCat.{u + 1} A)) :
    (ExternalRHom.constantPullbackIso A g₁₂).hom.app Z ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g₁ g₂ g₁₂ hg).hom.app
          ((ExternalRHom.constant A R').obj Z) =
      (ExternalRHom.constantPullbackIso A g₁).hom.app Z ≫
        (ExternalRHom.pull A g₁).map ((ExternalRHom.constantPullbackIso A g₂).hom.app Z) := by
  subst hg
  exact imageConstantPullback_comp A g₁ g₂ Z

/-- The left-adjoint comparisons `imageTensorIso` are compatible with inverse-image
composition, with `restrictTensorIso` for the comparison along `f.left`. -/
theorem imageTensorIso_hom_app_comp {T S : Over X} (f : T ⟶ S)
    (Q : DerivedCategory (ModuleCat.{u + 1} A)) :
    (imageTensorIso A K T).hom.app Q ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f.left S.hom T.hom f.w.symm).hom.app
          (K ⊗ (ExternalRHom.constant A X).obj Q) =
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f.left S.hom T.hom f.w.symm).hom.app K ▷
          (ExternalRHom.constant A T.left).obj Q) ≫
        (restrictTensorIso A f.left ((ExternalRHom.pull A S.hom).obj K)).hom.app Q ≫
        (ExternalRHom.pull A f.left).map ((imageTensorIso A K S).hom.app Q) := by
  rw [imageTensorIso_hom_app, restrictTensorIso_hom_app, imageTensorIso_hom_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [pullTensorIso_hom_comp, ← pullTensorIso_hom_natural_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc]
  erw [← constantPullbackIso_hom_comp A f.left S.hom T.hom f.w.symm Q]
  rw [MonoidalCategory.whiskerLeft_comp_assoc, tensorHom_def_assoc]
  erw [whisker_exchange_assoc]
  rfl

end AlgebraicGeometry.Etale.IndEtaleMapping
