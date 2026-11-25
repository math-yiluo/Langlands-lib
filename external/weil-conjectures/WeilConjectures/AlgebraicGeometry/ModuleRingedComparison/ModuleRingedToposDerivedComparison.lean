/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionDerivedRealization
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.AlgebraicGeometry.ModuleRingedToposDerivedComparison

import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.AlgebraicGeometry.SectionDerivedTensorNormalization

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
/-! # Module-object and ringed-topos derived comparison

## Main definitions and statements

- `ordinary_exact_flat_kflat`, `ordinary_monoidal`: the ordinary equivalence clauses.
- `derivedPullComparison`, `derivedPushComparison`, `derived_homEquiv`: derived operations.
- `tensorPullComparison`, `delta_comparison`, `mu_comparison`: specified tensor maps.
- `composition_comparison`, `projection_comparison`: composition and the proper mate.
- `open_homEquiv`, `openProjection_comparison`: open adjunction and its unit mate.

## References

* Stacks Project, Sites, Tag 00YV
* Modules on Sites, Tags 03EK, 03EL, 03D7, 03DI and 03DJ
* Cohomology on Sites, Tags 07A4, 07A6 and 0B56
-/

@[expose] public noncomputable section

set_option linter.all false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

private def curryComparison {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : C ⥤ C ⥤ C) (S : D × D ⥤ D)
    (t : Functor.uncurry.obj T ⋙ F ⟶ F.prod F ⋙ S) :
    (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (Functor.curry.obj S) where
  app M :=
    { app := fun N ↦ t.app (M, N)
      naturality := by
        intro N N' f
        simpa using t.naturality (Prod.mkHom (𝟙 M) f) }
  naturality := by
    intro M M' f
    ext N
    simpa using t.naturality (Prod.mkHom f (𝟙 N))

private theorem tensorSquare_right
    {C : Type*} [Category C] (T : C × C ⥤ C)
    {A B V W X X' Y Y' : C} (p : X ≅ X') (q : Y ≅ Y') (r : A ≅ B)
    (a : A ⟶ V) (b : V ⟶ T.obj (X, Y))
    (c : B ⟶ W) (d : W ⟶ T.obj (X', Y'))
    (h : a ≫ b ≫ T.map (Prod.mkHom p.hom q.hom) = r.hom ≫ c ≫ d) :
    c ≫ d ≫ T.map (Prod.mkHom p.inv (𝟙 Y')) ≫
        T.map (Prod.mkHom (𝟙 X) q.inv) = r.inv ≫ a ≫ b := by
  rw [← T.map_comp]
  simp only [prod_comp, Category.comp_id, Category.id_comp]
  rw [← cancel_epi r.hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← reassoc_of% h]
  simp only [← T.map_comp, prod_comp, Iso.hom_inv_id, ← prod_id,
    T.map_id, Category.comp_id]

private theorem mapIso_cancel_left {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} (e : X ≅ Y) {Z : D}
    (b : F.obj Y ⟶ Z) (c : F.obj X ⟶ Z) (h : b = F.map e.inv ≫ c) :
    F.map e.hom ≫ b = c := by
  rw [h, ← F.map_comp_assoc, e.hom_inv_id, F.map_id, Category.id_comp]

private theorem projection_comparison_of_squares
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    (F : C₂ ⥤ C₁) (G : C₁ ⥤ C₂) (adj : F ⊣ G)
    (F' : D₂ ⥤ D₁) (G' : D₁ ⥤ D₂) (adj' : F' ⊣ G')
    (E₁ : C₁ ⥤ D₁) (E₂ : C₂ ⥤ D₂)
    (T₁ : C₁ ⥤ C₁ ⥤ C₁) (T₂ : C₂ ⥤ C₂ ⥤ C₂)
    (S₁ : D₁ × D₁ ⥤ D₁) (S₂ : D₂ × D₂ ⥤ D₂)
    (p : F ⋙ E₁ ≅ E₂ ⋙ F') (q : G ⋙ E₂ ≅ E₁ ⋙ G')
    (c₁ : Functor.uncurry.obj T₁ ⋙ E₁ ≅ E₁.prod E₁ ⋙ S₁)
    (c₂ : Functor.uncurry.obj T₂ ⋙ E₂ ≅ E₂.prod E₂ ⋙ S₂)
    (δ : (Functor.postcompose₂.obj F).obj T₂ ⟶
      (((Functor.whiskeringLeft₂ C₁).obj F).obj F).obj T₁)
    (δ' : S₂ ⋙ F' ≅ F'.prod F' ⋙ S₁)
    (hδ : ∀ M N,
      E₁.map ((δ.app M).app N) ≫ c₁.hom.app (F.obj M, F.obj N) ≫
          S₁.map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
        p.hom.app ((T₂.obj M).obj N) ≫ F'.map (c₂.hom.app (M, N)) ≫
          δ'.hom.app (E₂.obj M, E₂.obj N))
    (hCounit : ∀ A, adj'.counit.app (E₁.obj A) =
      F'.map (q.inv.app A) ≫ p.inv.app (G.obj A) ≫ E₁.map (adj.counit.app A))
    (K : C₁) (L : C₂) :
    E₂.map (adj.homEquiv _ _
        (((δ.app (G.obj K)).app L) ≫ (T₁.map (adj.counit.app K)).app (F.obj L))) ≫
        q.hom.app ((T₁.obj K).obj (F.obj L)) ≫
        G'.map (c₁.hom.app (K, F.obj L)) ≫
        G'.map (S₁.map (Prod.mkHom (𝟙 (E₁.obj K)) (p.hom.app L))) =
      c₂.hom.app (G.obj K, L) ≫
        S₂.map (Prod.mkHom (q.hom.app K) (𝟙 (E₂.obj L))) ≫
        derivedProjectionFormulaMate F' G' adj' S₂ S₁ δ' (E₁.obj K) (E₂.obj L) := by
  let d := Functor.curry.map δ'.hom ≫
    (Functor.curryObjProdComp F' F'
      S₁).hom
  let tX := curryComparison E₁
    T₁ S₁
    c₁.hom
  let tY := curryComparison E₂
    T₂ S₂
    c₂.hom
  have hs : ∀ M N,
      F'.map ((tY.app M).app N) ≫
        (d.app (E₂.obj M)).app
          (E₂.obj N) ≫
        ((Functor.curry.obj S₁).map
          (p.inv.app M)).app _ ≫
        ((Functor.curry.obj S₁).obj _).map
          (p.inv.app N) =
      p.inv.app _ ≫
        E₁.map ((δ.app M).app N) ≫
        (tX.app _).app _ := by
    intro M N
    change F'.map
        (c₂.hom.app (M, N)) ≫
      (δ'.hom.app
        (E₂.obj M,
          E₂.obj N) ≫ 𝟙 _) ≫
      S₁.map (Prod.mkHom (p.inv.app M) (𝟙 _)) ≫
      S₁.map (Prod.mkHom (𝟙 _) (p.inv.app N)) =
      p.inv.app _ ≫
        E₁.map ((δ.app M).app N) ≫
        c₁.hom.app
          (F.obj M, F.obj N)
    simp only [Category.comp_id]
    exact tensorSquare_right S₁
      (p.app M) (p.app N)
      (p.app
        ((T₂.obj M).obj N))
      (E₁.map ((δ.app M).app N))
      (c₁.hom.app
        (F.obj M, F.obj N))
      (F'.map (c₂.hom.app (M, N)))
      (δ'.hom.app
        (E₂.obj M, E₂.obj N))
      (hδ M N)
  have hc (A : C₁) :
      F'.map (q.hom.app A) ≫ adj'.counit.app (E₁.obj A) =
        p.inv.app (G.obj A) ≫ E₁.map (adj.counit.app A) :=
    mapIso_cancel_left F' (q.app A) _ _ (hCounit A)
  have h := Adjunction.rightAdjointProjectionMap_mate
    adj adj'
    (T₂ := Functor.curry.obj S₁) (S₂ := Functor.curry.obj S₂)
    (U := E₂) (V := E₁)
    δ d tY tX p.inv
    q.hom hs hc K L
  have hh := congrArg (fun q ↦ q ≫ G'.map
    (S₁.map (Prod.mkHom (𝟙 (E₁.obj K))
      (p.hom.app L)))) h
  dsimp only [tX, tY, curryComparison] at hh
  change (E₂.map ((adj.homEquiv _ _
        (((δ.app (G.obj K)).app L) ≫ (T₁.map (adj.counit.app K)).app (F.obj L)))) ≫
      q.hom.app _ ≫
      G'.map (c₁.hom.app
        (K, F.obj L))) ≫
      G'.map (S₁.map (Prod.mkHom (𝟙 _)
        (p.hom.app L))) =
    (c₂.hom.app (G.obj K, L) ≫
      S₂.map (Prod.mkHom (q.hom.app K) (𝟙 _)) ≫
      derivedProjectionFormulaMate F' G' adj' S₂ S₁ δ' (E₁.obj K)
        (E₂.obj L) ≫
      G'.map (S₁.map (Prod.mkHom (𝟙 _)
        (p.inv.app L)))) ≫
      G'.map (S₁.map (Prod.mkHom (𝟙 _)
        (p.hom.app L))) at hh
  simp only [Category.assoc, ← G'.map_comp,
    ← S₁.map_comp, prod_comp, Category.id_comp, Iso.inv_hom_id_app,
    ← prod_id] at hh
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.comp_id] at hh
  simpa only [Functor.id_obj, G'.map_comp] using hh

private theorem third_conjunct {P Q R S : Prop} (h : P ∧ Q ∧ R ∧ S) : R :=
  h.2.2.1

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

variable [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]

-- The comparison instances contain large sheaf tensor constraints.
-- Comparing the two localized mate squares elaborates the section-module constraints.
/-- The ringed adjoint-of-unit open projection arrow, using inverse canonical delta. -/
def openProjection {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory (modules Λ U)) (L : DerivedCategory (modules Λ X)) :
    (derivedExtension Λ j).obj ((tensor Λ U).obj (K, (derivedPullback Λ j).obj L)) ⟶
      (tensor Λ X).obj ((derivedExtension Λ j).obj K, L) :=
  ((derivedOpenAdjunction Λ j).homEquiv _ _).symm
    ((tensor Λ U).map (Prod.mkHom ((derivedOpenAdjunction Λ j).unit.app K)
        (𝟙 ((derivedPullback Λ j).obj L))) ≫
      (tensorPullComparison Λ j).inv.app ((derivedExtension Λ j).obj K, L))

-- The curried tensor and derived adjunction interfaces have large instance arguments.
/-- Pullback composition is identified with the canonical ringed pasting comparison. -/
theorem composition_comparison {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∀ M : DerivedCategory (internalModules Λ Z),
        (derivedPullComparison Λ (f ≫ g)).hom.app M ≫
            (derivedPullbackComposition Λ f g).hom.app ((derivedEquivalence Λ Z).functor.obj M) =
          (derivedEquivalence Λ X).functor.map
              ((CondensedRing.leftDerivedUpperStarComp Λ f g).hom.app M) ≫
            (derivedPullComparison Λ f).hom.app
              ((internalDerivedPullback Λ g).obj M) ≫
            (derivedPullback Λ f).map ((derivedPullComparison Λ g).hom.app M) := by
  exact (sectionDerivedPushpullNormalization Λ f).2.2.2.2.2.2.2.2.2.1 g

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
