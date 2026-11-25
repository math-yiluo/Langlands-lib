/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# Derived direct image of a degreewise split sequence of K-injectives

Source: Stacks Project, Tags 0152 and 079V
(blueprint: lem-pc-derived-functor-termwise-split-ses-triangle).
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}
  [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
  [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]

/-- The identification computed by the identity resolution of a K-injective complex.
It is the inverse right-derived unit, with the quotient/localization identifications.
Source: Stacks, Tag 079V
(blueprint: lem-pc-derived-functor-termwise-split-ses-triangle). -/
def derivedModuleDirectImageKInjectiveIso (g : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) [K.IsKInjective] :
    (derivedModuleDirectImage g).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (derivedModuleDirectImage g).mapIso
      ((DerivedCategory.quotientCompQhIso _).app K).symm ≪≫
    (asIso ((moduleDirectImage g).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj K))).symm ≪≫
    DerivedCategory.Qh.mapIso
      (((moduleDirectImage g).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

/-- The identification of the localized image of a shifted complex with the shifted
localized image. Both complex shift comparison maps are degreewise identities.
Source: Stacks, Tags 0152 and 079V
(blueprint: lem-pc-derived-functor-termwise-split-ses-triangle). -/
def moduleDirectImageLocalizedShiftIso (g : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) :
    DerivedCategory.Q.obj
        (((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)).obj (K⟦(1 : ℤ)⟧)) ≅
      (DerivedCategory.Q.obj
        (((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.mapIso
      ((((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso
        (1 : ℤ)).app K) ≪≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).app _

/-- The triangle with the connecting map transported by the identity-resolution comparisons.
Source: Stacks, Tags 0152 and 079V
(blueprint: lem-pc-derived-functor-termwise-split-ses-triangle). -/
def derivedModuleDirectImageSplitTriangle (g : X ⟶ Y)
    (S : ShortComplex (CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ))
    (hS : S.ShortExact) [S.X₁.IsKInjective] [S.X₂.IsKInjective] [S.X₃.IsKInjective] :
    Triangle (DerivedCategory (SheafOfModules.{u} (moduleRings Y))) :=
  Triangle.mk
    ((derivedModuleDirectImage g).map (DerivedCategory.Q.map S.f))
    ((derivedModuleDirectImage g).map (DerivedCategory.Q.map S.g))
    ((derivedModuleDirectImage g).map (DerivedCategory.triangleOfSESδ hS) ≫
      (derivedModuleDirectImage g).map
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app S.X₁) ≫
      (derivedModuleDirectImageKInjectiveIso g (S.X₁⟦(1 : ℤ)⟧)).hom ≫
      (moduleDirectImageLocalizedShiftIso g S.X₁).hom ≫
      (shiftFunctor _ (1 : ℤ)).map (derivedModuleDirectImageKInjectiveIso g S.X₁).inv)

private def directImageComparison (g : X ⟶ Y) :
    (moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedModuleDirectImage g :=
  (Functor.isoWhiskerLeft
    ((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ))
    (DerivedCategory.quotientCompQhIso _)).inv ≫
  (Functor.isoWhiskerRight
    ((moduleDirectImage g).mapHomotopyCategoryFactors (ComplexShape.up ℤ))
    DerivedCategory.Qh).inv ≫
  Functor.whiskerLeft (HomotopyCategory.quotient _ _)
    (moduleDirectImage g).rightDerivedFunctorUnit ≫
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _)
    (derivedModuleDirectImage g)).hom

private lemma directImageComparison_app (g : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) [K.IsKInjective] :
    (directImageComparison g).app K = (derivedModuleDirectImageKInjectiveIso g K).inv := by
  simp [directImageComparison, derivedModuleDirectImageKInjectiveIso]

private lemma directImageComparison_naturality (g : X ⟶ Y)
    {K L : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ}
    [K.IsKInjective] [L.IsKInjective] (f : K ⟶ L) :
    (derivedModuleDirectImage g).map (DerivedCategory.Q.map f) ≫
        (derivedModuleDirectImageKInjectiveIso g L).hom =
      (derivedModuleDirectImageKInjectiveIso g K).hom ≫
        DerivedCategory.Q.map
          (((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have h := (directImageComparison g).naturality f
  simp only [Functor.comp_map, directImageComparison_app] at h
  rw [← cancel_epi (derivedModuleDirectImageKInjectiveIso g K).inv,
    Iso.inv_hom_id_assoc, ← Category.assoc, ← h, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

private lemma comparison_boundary_of_epi
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ D) (R : D ⥤ E) (F : C ⥤ E) (α : F ⟶ Q ⋙ R)
    {K L M : C} (d : K ⟶ L) (t : K ⟶ M) [Epi (F.map d)]
    (eL : R.obj (Q.obj L) ≅ F.obj L) (eM : R.obj (Q.obj M) ≅ F.obj M)
    (hL : α.app L = eL.inv) (hM : α.app M = eM.inv)
    (b : Q.obj L ⟶ Q.obj M) (hdt : Q.map d ≫ b = Q.map t)
    {N : E} (s : F.obj M ⟶ N) (δ : F.obj L ⟶ N)
    (hδ : F.map d ≫ δ = F.map t ≫ s) :
    R.map b ≫ eM.hom ≫ s = eL.hom ≫ δ := by
  have ht := α.naturality t
  simp only [Functor.comp_map] at ht
  apply (cancel_epi eL.inv).mp
  rw [eL.inv_hom_id_assoc, ← hL]
  apply (cancel_epi (F.map d)).mp
  rw [← Category.assoc, α.naturality]
  change (α.app K ≫ R.map (Q.map d)) ≫ (R.map b ≫ eM.hom ≫ s) = F.map d ≫ δ
  rw [Category.assoc, ← R.map_comp_assoc, hdt, ← Category.assoc, ← ht]
  rw [Category.assoc, hM, eM.inv_hom_id_assoc]
  exact hδ.symm

-- Cone comparison identities elaborate through the module-sheaf instances.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma directImage_boundary {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))] (g : X ⟶ Y)
    (S : ShortComplex (CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ))
    (hImage : (S.map
      ((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ))).ShortExact) :
    DerivedCategory.Q.map
        (((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (CochainComplex.mappingCone.descShortComplex S)) ≫
        DerivedCategory.triangleOfSESδ hImage =
      DerivedCategory.Q.map
        (((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (CochainComplex.mappingCone.triangle S.f).mor₃) ≫
        (moduleDirectImageLocalizedShiftIso g S.X₁).hom := by
  let F := (moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)
  let Q := DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings Y))
  let c := (CochainComplex.mappingCone.mapHomologicalComplexIso S.f (moduleDirectImage g)).hom
  let d := CochainComplex.mappingCone.descShortComplex (S.map F)
  let t := (CochainComplex.mappingCone.triangle (F.map S.f)).mor₃
  let s := (Q.commShiftIso (1 : ℤ)).hom.app (F.obj S.X₁)
  calc
    _ = Q.map (c ≫ d) ≫ DerivedCategory.triangleOfSESδ hImage :=
      congrArg (fun f ↦ Q.map f ≫ DerivedCategory.triangleOfSESδ hImage)
        (CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex
          (moduleDirectImage g) S).symm
    _ = Q.map c ≫ (Q.map d ≫ DerivedCategory.triangleOfSESδ hImage) :=
      Q.map_comp_assoc c d _
    _ = Q.map c ≫ (Q.map t ≫ s) :=
      congrArg (fun f ↦ Q.map c ≫ f)
        (DerivedCategory.descShortComplex_triangleOfSESδ hImage)
    _ = Q.map (c ≫ t) ≫ s := (Q.map_comp_assoc c t s).symm
    _ = Q.map (F.map (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
        (F.commShiftIso (1 : ℤ)).hom.app S.X₁) ≫ s :=
      congrArg (fun f ↦ Q.map f ≫ s)
        (CochainComplex.mappingCone.map_δ S.f (moduleDirectImage g)).symm
    _ = _ := Q.map_comp_assoc _ _ _

-- Naturality and cancellation involve several nested derived and shift functors.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Degreewise split sequences of K-injectives have their canonical triangle carried to
that of the direct-image sequence, including its connecting morphism.
Source: Stacks, Tags 0152 and 079V
(blueprint: lem-pc-derived-functor-termwise-split-ses-triangle).

Proof:
1. Apply additive module direct image to the degreewise retraction and section identities.
This preserves split exactness. Additivity also preserves the negative differential in
shift by one. The boundary is the chain map pi d s, with the cone sign convention, by
lem-weil-pbc-degreewise-split-connecting-morphism and
lem-weil-pbc-degreewise-split-derived-triangle. Its direct image is g-star(pi d s).
2. Shifts of K-injectives are K-injective, since shifting preserves acyclicity and the
Hom groups from acyclic objects vanish. The inverse right-derived unit on K-injectives
is natural, by def-pc-ringed-spaces-derived-direct-image. Apply this to the first two
maps and to pi d s. After localization this gives all three comparison identities.
3. The image sequence has a distinguished triangle by lem-weil-pbc-complex-ses-triangle.
The three comparison isomorphisms form an isomorphism from the displayed transported
triangle to that triangle, including the third map by step 2. Closure under isomorphism
in def-weil-triangulated-category proves distinguishedness.

The node's clauses that I₁[1] is K-injective and that g-star(I₁[1]) = (g-star I₁)[1]
are not separate conjuncts: the first is Mathlib's shift instance for
`CochainComplex.IsKInjective` (used to form the comparison of `S.X₁⟦1⟧`), the second holds
by `rfl` for termwise direct image, and its canonical `commShiftIso` (identity components,
`Functor.mapHomologicalComplex_commShiftIso_hom_app_f`) is the identification used in
`moduleDirectImageLocalizedShiftIso`. -/
theorem derivedModuleDirectImage_termwise_split_ses_triangle (g : X ⟶ Y)
    (S : ShortComplex (CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ))
    (hS : S.ShortExact)
    (_hSplit : ∀ n : ℤ, Nonempty ((S.map
      (HomologicalComplex.eval (SheafOfModules.{u} (moduleRings X))
        (ComplexShape.up ℤ) n)).Splitting))
    [S.X₁.IsKInjective] [S.X₂.IsKInjective] [S.X₃.IsKInjective] :
    ∃ hImage : (S.map
      ((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ))).ShortExact,
      (∀ n : ℤ, Nonempty (((S.map
        ((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ))).map
        (HomologicalComplex.eval (SheafOfModules.{u} (moduleRings Y))
          (ComplexShape.up ℤ) n)).Splitting)) ∧
      ((derivedModuleDirectImage g).map (DerivedCategory.Q.map S.f) ≫
          (derivedModuleDirectImageKInjectiveIso g S.X₂).hom =
        (derivedModuleDirectImageKInjectiveIso g S.X₁).hom ≫
          DerivedCategory.Q.map
            (((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)).map S.f)) ∧
      ((derivedModuleDirectImage g).map (DerivedCategory.Q.map S.g) ≫
          (derivedModuleDirectImageKInjectiveIso g S.X₃).hom =
        (derivedModuleDirectImageKInjectiveIso g S.X₂).hom ≫
          DerivedCategory.Q.map
            (((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)).map S.g)) ∧
      ((derivedModuleDirectImage g).map (DerivedCategory.triangleOfSESδ hS) ≫
          (derivedModuleDirectImage g).map
            ((DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app S.X₁) ≫
          (derivedModuleDirectImageKInjectiveIso g (S.X₁⟦(1 : ℤ)⟧)).hom ≫
          (moduleDirectImageLocalizedShiftIso g S.X₁).hom =
        (derivedModuleDirectImageKInjectiveIso g S.X₃).hom ≫
          DerivedCategory.triangleOfSESδ hImage) ∧
      (∃ e : derivedModuleDirectImageSplitTriangle g S hS ≅
          DerivedCategory.triangleOfSES hImage,
        e.hom.hom₁ = (derivedModuleDirectImageKInjectiveIso g S.X₁).hom ∧
        e.hom.hom₂ = (derivedModuleDirectImageKInjectiveIso g S.X₂).hom ∧
        e.hom.hom₃ = (derivedModuleDirectImageKInjectiveIso g S.X₃).hom) ∧
      derivedModuleDirectImageSplitTriangle g S hS ∈
        distTriang (DerivedCategory (SheafOfModules.{u} (moduleRings Y))) := by
  classical
  let F := (moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)
  have hSplit : ∀ n : ℤ, Nonempty (((S.map F).map
      (HomologicalComplex.eval (SheafOfModules.{u} (moduleRings Y))
        (ComplexShape.up ℤ) n)).Splitting) := by
    intro n
    exact ⟨(_hSplit n).some.map (moduleDirectImage g)⟩
  have hImage : (S.map F).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n ↦
      ShortComplex.ShortExact.mk' (hSplit n).some.exact
        (hSplit n).some.mono_f (hSplit n).some.epi_g)
  have hf := directImageComparison_naturality g S.f
  have hg := directImageComparison_naturality g S.g
  have hδ : (derivedModuleDirectImage g).map (DerivedCategory.triangleOfSESδ hS) ≫
      (derivedModuleDirectImage g).map
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app S.X₁) ≫
      (derivedModuleDirectImageKInjectiveIso g (S.X₁⟦(1 : ℤ)⟧)).hom ≫
      (moduleDirectImageLocalizedShiftIso g S.X₁).hom =
    (derivedModuleDirectImageKInjectiveIso g S.X₃).hom ≫
      DerivedCategory.triangleOfSESδ hImage := by
    let d := CochainComplex.mappingCone.descShortComplex S
    let t : CochainComplex.mappingCone S.f ⟶ S.X₁⟦(1 : ℤ)⟧ :=
      (CochainComplex.mappingCone.triangle S.f).mor₃
    have hd : IsIso ((F ⋙ DerivedCategory.Q).map d) := by
      change IsIso (DerivedCategory.Q.map (F.map d))
      dsimp [d, F]
      rw [← CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex,
        Functor.map_comp]
      have := CochainComplex.mappingCone.quasiIso_descShortComplex hImage
      infer_instance
    have hdt : DerivedCategory.Q.map d ≫ DerivedCategory.triangleOfSESδ hS ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app S.X₁ =
      DerivedCategory.Q.map t := by
      dsimp [d, t]
      rw [DerivedCategory.descShortComplex_triangleOfSESδ_assoc, Iso.hom_inv_id_app]
      exact Category.comp_id _
    simpa only [Functor.map_comp, Category.assoc] using
      comparison_boundary_of_epi DerivedCategory.Q (derivedModuleDirectImage g)
        (F ⋙ DerivedCategory.Q) (directImageComparison g) d t
        (derivedModuleDirectImageKInjectiveIso g S.X₃)
        (derivedModuleDirectImageKInjectiveIso g (S.X₁⟦(1 : ℤ)⟧))
        (directImageComparison_app g S.X₃)
        (directImageComparison_app g (S.X₁⟦(1 : ℤ)⟧))
        (DerivedCategory.triangleOfSESδ hS ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app S.X₁) hdt
        (moduleDirectImageLocalizedShiftIso g S.X₁).hom
        (DerivedCategory.triangleOfSESδ hImage) (directImage_boundary g S hImage)
  let e : derivedModuleDirectImageSplitTriangle g S hS ≅
      DerivedCategory.triangleOfSES hImage :=
    Triangle.isoMk _ _ (derivedModuleDirectImageKInjectiveIso g S.X₁)
      (derivedModuleDirectImageKInjectiveIso g S.X₂)
      (derivedModuleDirectImageKInjectiveIso g S.X₃) hf hg (by
        dsimp only [derivedModuleDirectImageSplitTriangle, DerivedCategory.triangleOfSES,
          Triangle.mk_mor₃]
        have he := ((shiftFunctor
          (DerivedCategory (SheafOfModules.{u} (moduleRings Y))) (1 : ℤ)).mapIso
          (derivedModuleDirectImageKInjectiveIso g S.X₁)).inv_hom_id
        dsimp only [Functor.mapIso_hom, Functor.mapIso_inv] at he
        simpa only [Category.assoc, he, Category.comp_id] using hδ)
  exact ⟨hImage, hSplit, hf, hg, hδ, ⟨e, rfl, rfl, rfl⟩,
    isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hImage) _ e⟩

end AlgebraicGeometry.RingedSpace
