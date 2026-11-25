/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCompositionCounitApex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedMateEvaluation

/-! # Localized underived counits and the derived composition comparison
Source: Stacks Project, Tags 0096, 079W and 0D5S.
(blueprint: lem-sc-derived-pullback-composition-localized-counit).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
set_option backward.defeqAttrib.useBackward true
universe u w
open CategoryTheory
namespace AlgebraicGeometry
attribute [local irreducible] Scheme.Modules.tensorPullback DerivedCategory.Qh
  canonicalDerivedPullbackComposition
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] Scheme.Modules.Hom Scheme.Modules.instCategory
  Scheme.Modules.instAbelian HomotopyCategory DerivedCategory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Descend the ordinary mate counit equation degreewise to the homotopy category.
private theorem composite_counit
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    [Limits.HasBinaryBiproducts C] [Limits.HasBinaryBiproducts D]
    [Limits.HasBinaryBiproducts E]
    {L₁ : D ⥤ C} {R₁ : C ⥤ D} {L₂ : E ⥤ D} {R₂ : D ⥤ E}
    {L : E ⥤ C} {R : C ⥤ E}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [L.Additive] [R.Additive]
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a : L ⊣ R)
    (e : R₁ ⋙ R₂ ≅ R) (K : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso
        ((conjugateIsoEquiv a (a₂.comp a₁)).symm e.symm) (.up ℤ)).hom.app
          ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
        (a.mapHomotopyCategory (.up ℤ)).counit.app K =
      (L₁.mapHomotopyCategory (.up ℤ)).map
          ((L₂.mapHomotopyCategory (.up ℤ)).map
              ((NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app K) ≫
            (a₂.mapHomotopyCategory (.up ℤ)).counit.app
              ((R₁.mapHomotopyCategory (.up ℤ)).obj K)) ≫
        (a₁.mapHomotopyCategory (.up ℤ)).counit.app K := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  erw [Adjunction.mapHomotopyCategory_counit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  let Q := HomotopyCategory.quotient C (.up ℤ)
  change Q.map _ ≫ Q.map _ = Q.map _ ≫ Q.map _
  rw [← Q.map_comp, ← Q.map_comp]
  congr 1
  ext n : 1
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplex_map_f, Adjunction.mapHomologicalComplex_counit_app_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.map_comp]
  dsimp only [HomotopyCategory.quotient_obj_as, Functor.mapHomologicalComplex]
  simpa only [conjugateIsoEquiv_symm_apply_hom, Iso.symm_hom,
    Adjunction.comp_counit_app, Functor.comp_map, Category.assoc] using
    (conjugateEquiv_counit_symm a (a₂.comp a₁) e.inv (P.X n)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The left-derived universal property and naturality paste the two counits.
private theorem localized_counit
    {A B C A' B' C' : Type*}
    [Category* A] [Category* B] [Category* C]
    [Category* A'] [Category* B'] [Category* C']
    (QA : A ⥤ A') (QB : B ⥤ B') (QC : C ⥤ C')
    (T₁ : B ⥤ A) (T₂ : C ⥤ B) (T : C ⥤ A)
    (F₁ : B' ⥤ A') (F₂ : C' ⥤ B') (F : C' ⥤ A')
    (ε₁ : QB ⋙ F₁ ⟶ T₁ ⋙ QA) (ε₂ : QC ⋙ F₂ ⟶ T₂ ⋙ QB)
    (ε : QC ⋙ F ⟶ T ⋙ QA) (e : T₂ ⋙ T₁ ⟶ T)
    (W : MorphismProperty C) [QC.IsLocalization W] [F.IsLeftDerivedFunctor ε W]
    (p : F₂ ⋙ F₁ ⟶ F)
    (hp : p = F.leftDerivedLift ε W (F₂ ⋙ F₁)
      ((Functor.associator QC F₂ F₁).inv ≫
        Functor.whiskerRight ε₂ F₁ ≫ (Functor.associator T₂ QB F₁).hom ≫
        Functor.whiskerLeft T₂ ε₁ ≫ (Functor.associator T₂ T₁ QA).inv ≫
        Functor.whiskerRight e QA))
    (M : C) (H : B) (K : A) (d : T₂.obj M ⟶ H) (t : T₁.obj H ⟶ K)
    (c : T.obj M ⟶ K) (hc : e.app M ≫ c = T₁.map d ≫ t) :
    p.app (QC.obj M) ≫ ε.app M ≫ QA.map c =
      F₁.map (ε₂.app M ≫ QB.map d) ≫ ε₁.app H ≫ QA.map t := by
  rw [hp, ← Category.assoc, Functor.leftDerived_fac_app]
  simp only [NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp]
  rw [Category.assoc, Category.assoc, ← QA.map_comp, hc, QA.map_comp]
  have hn := ε₁.naturality d
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  simp only [Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The pushforward composition comparison is the identity on sections.
private theorem pushforward_comparison_inv
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory X.Modules (.up ℤ)) :
    (NatTrans.mapHomotopyCategory (Scheme.Modules.pushforwardComp f g).inv
      (.up ℤ)).app K =
      𝟙 (((Scheme.Modules.pushforward (f ≫ g)).mapHomotopyCategory (.up ℤ)).obj K) := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  let Q := HomotopyCategory.quotient Z.Modules (.up ℤ)
  have h0 : (NatTrans.mapHomologicalComplex (Scheme.Modules.pushforwardComp f g).inv
      (.up ℤ)).app P = 𝟙 _ := by
    ext n U
    rfl
  exact (congrArg Q.map h0).trans (Q.map_id _)

variable [∀ S : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]

set_option linter.style.haveILetI false in
-- Inlining these instance proofs avoids costly let-bound instance comparisons.
-- The composite pushforward objects require dependent sheaf type comparisons.
/-- The left-derived lift equation followed by the localized underived composite
counit equals the pasted underived expression. This calculation involves no
right-derived unit or selected derived pullback/direct-image adjunction.
Source: Stacks Project, Tags 0096, 079W and 0D5S; steps 2 and 3 of
lem-sc-derived-pullback-composition-counit-normalization.
(blueprint: lem-sc-derived-pullback-composition-localized-counit).

Proof: The last chosen witness of exists_derivedPullbackComposition identifies
p.hom with the leftDerivedLift of the counits followed by the mapped inverse mate
of pushforwardComp. Its preceding witness says epsilon(fg) is a left-derived
counit. Apply Functor.leftDerived_fac_app and precompose the localized underived
counit. Expand the associator and whiskering components, removing identity maps.
At each degree, conjugateEquiv_counit_symm for the tensor adjunctions and
pushforwardComp.inv identifies the inverse mate followed by the (fg)-counit
with tensor pullback by f of the g-counit followed by the f-counit;
pushforwardComp.inv is the identity on sections. Map this natural equality
through the homotopy quotient and DerivedCategory.Qh. Naturality of epsilon(f)
at the g-counit moves Q of its tensor pullback past epsilon(f). Functor.map_comp
then combines the two Lf images and yields derivedCompositionCounitApex_eq.
This argument is valid for all complexes, without boundedness or K-flatness:
it is a universal-property and naturality calculation. Identity morphisms,
zero complexes, zero rings and empty schemes satisfy the same equations. -/
theorem derivedPullbackComposition_localized_counit
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    let ε {A B : Scheme.{u}} (s : A ⟶ B) :=
      (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) s
    let b {A B : Scheme.{u}} (s : A ⟶ B) :=
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction s)).mapHomotopyCategory
        (ComplexShape.up ℤ)
    (canonicalDerivedPullbackComposition f g).hom.app
        (DerivedCategory.Qh.obj
          (((Scheme.Modules.pushforward (f ≫ g)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K)) ≫
      (ε (f ≫ g)).app
        (((Scheme.Modules.pushforward (f ≫ g)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((b (f ≫ g)).counit.app K) =
      derivedCompositionCounitApex f g K := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  classical
  letI : Limits.HasBinaryBiproducts X.Modules := inferInstance
  letI : Limits.HasBinaryBiproducts Y.Modules := inferInstance
  letI : Limits.HasBinaryBiproducts Z.Modules := inferInstance
  letI := (Classical.choose exists_derivedPullbackComposition.{u, w}) f
  letI := (Classical.choose exists_derivedPullbackComposition.{u, w}) g
  letI := (Classical.choose exists_derivedPullbackComposition.{u, w}) (f ≫ g)
  let ε {A B : Scheme.{u}} (s : A ⟶ B) :=
    (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) s
  let a {A B : Scheme.{u}} (s : A ⟶ B) :=
    Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction s)
  let b {A B : Scheme.{u}} (s : A ⟶ B) := (a s).mapHomotopyCategory (.up ℤ)
  let H := ((Scheme.Modules.pushforward f).mapHomotopyCategory (.up ℤ)).obj K
  let M := ((Scheme.Modules.pushforward (f ≫ g)).mapHomotopyCategory (.up ℤ)).obj K
  let δ := (conjugateIsoEquiv (a (f ≫ g)) ((a g).comp (a f))).symm
    (Scheme.Modules.pushforwardComp f g).symm
  let τ := Functor.mapHomotopyCategoryCompIso δ (.up ℤ)
  have hC := composite_counit
    (C := X.Modules) (D := Y.Modules) (E := Z.Modules)
    (a f) (a g) (a (f ≫ g))
    (Scheme.Modules.pushforwardComp f g) K
  simp only [pushforward_comparison_inv, CategoryTheory.Functor.map_id,
    Category.id_comp] at hC
  letI := (Classical.choose (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) (f ≫ g)
  have hc := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))).1 f g
  have ht := localized_counit
    (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings Z.toRingedSpace)))
    ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ))
    ((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ))
    ((Scheme.Modules.tensorPullback (f ≫ g)).mapHomotopyCategory (.up ℤ))
    (derivedPullback f) (derivedPullback g) (derivedPullback (f ≫ g))
    (ε f) (ε g) (ε (f ≫ g)) τ.hom
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ))
    (canonicalDerivedPullbackComposition f g).hom
    (by simpa only [canonicalDerivedPullbackComposition, ε, a, τ, δ] using hc) M H K
    ((b g).counit.app H) ((b f).counit.app K) ((b (f ≫ g)).counit.app K) hC
  exact ht.trans (derivedCompositionCounitApex_eq f g K).symm

end AlgebraicGeometry
