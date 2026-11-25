/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralBoundaryData

/-! # Integral normalization for Chern data with variable coefficient towers -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u u₁ v₁ u₂ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

private theorem normalizedExtension_arrow
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    {X Z Q P₀ P₁ W : C} {Y V : D}
    (e : F.obj X ≅ Y) (t : F.obj Z ≅ V) (σ : G.obj Y ≅ Q)
    (q : X ⟶ Q) (p₀ : G.obj V ⟶ P₀) (p₁ : P₀ ⟶ P₁) (p₂ : P₁ ⟶ W)
    (b : Z ⟶ W)
    (he : (a.homEquiv _ _) e.hom ≫ σ.hom = q)
    (ht : (a.homEquiv _ _) t.hom ≫ p₀ ≫ p₁ ≫ p₂ = b) (f : X ⟶ Z) :
    q ≫ (σ.inv ≫ G.map (e.inv ≫ F.map f ≫ t.hom) ≫ p₀ ≫ p₁) ≫ p₂ =
      f ≫ b := by
  have htransport : (a.homEquiv _ _) e.hom ≫
      G.map (e.inv ≫ F.map f ≫ t.hom) = f ≫ (a.homEquiv _ _) t.hom := by
    rw [← Adjunction.homEquiv_naturality_right]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact a.homEquiv_naturality_left f t.hom
  calc
    _ = ((a.homEquiv _ _) e.hom ≫ G.map (e.inv ≫ F.map f ≫ t.hom)) ≫
        p₀ ≫ p₁ ≫ p₂ := by
      rw [← he]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by
      rw [htransport]
      simpa only [Category.assoc] using congrArg (fun z ↦ f ≫ z) ht

private theorem normalizedDerivedExtension_arrow
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (r : DerivedExtension F G) (s : ShortComplex C) (hs : s.ShortExact)
    {X : C} {Y V : D}
    (e : r.derived.obj ((DerivedCategory.singleFunctor C 0).obj X) ≅
      (DerivedCategory.singleFunctor D 0).obj Y)
    (t : r.derived.obj
      (((DerivedCategory.singleFunctor C 0).obj s.X₃)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor D 0).obj V)⟦(2 : ℤ)⟧)
    (y : G.obj V ≅ s.X₁) (q : X ⟶ G.obj Y)
    (he : r.sourceNormalization e q) (ht : r.targetNormalization s hs t y)
    (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj s.X₃)⟦(1 : ℤ)⟧) :
    underlyingSingleArrow G q y.hom (e.inv ≫ r.derived.map f ≫ t.hom) =
      f ≫ positiveExactBoundary s hs := by
  unfold underlyingSingleArrow
  exact normalizedExtension_arrow r.derivedAdjunction e t
    ((G.mapDerivedCategorySingleFunctor 0).app Y)
    ((DerivedCategory.singleFunctor C 0).map q)
    ((G.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor D 0).obj V))
    (((G.mapDerivedCategorySingleFunctor 0).hom.app V)⟦(2 : ℤ)⟧')
    (((DerivedCategory.singleFunctor C 0).map y.hom)⟦(2 : ℤ)⟧')
    (hs.singleδ⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd (DerivedCategory C) (1 : ℤ) 1).inv.app
        ((DerivedCategory.singleFunctor C 0).obj s.X₁)) he ht f

/-- The integral reduction of any arrow is its normalized boundary composite.

Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2),
integral reduction and the positive Kummer connecting morphism.
(blueprint: lem-sfb-chern-data-integral-normalization).

Proof: move the source-normalized integer generator through the derived
adjunction. Naturality cancels the unit comparison and moves the given arrow
outside the adjunct. The target normalization identifies the remaining adjunct
with the positive Kummer boundary, including its shift-addition comparison.
This is a calculation with the actual reduction model of c. Only the first two
fields of the supplied normalization record are used. Its scalar field and finite
evaluation play no role in this calculation. -/
theorem integralArrow_of_normalized (l : ℕ) [Fact l.Prime]
    {T : Scheme.{u}}
    (R A : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (φ : WeilConjectures.SemilinearSections.systemRing.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (fun n ↦ R.obj (op n))
        (fun n ↦ R.map (homOfLE (Nat.le_succ n)).op) ⟶
      WeilConjectures.SemilinearSections.systemRing.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (fun n ↦ A.obj (op n))
        (fun n ↦ A.map (homOfLE (Nat.le_succ n)).op))
    (c : ChernData l T R A φ)
    (q : coefficient T R ⟶
      (WeilConjectures.SemilinearSections.res.{u + 1, u, u + 1} φ).obj (coefficient T A))
    (hc : ChernData.Normalized l T R A φ c q)
    (f : (DerivedCategory.singleFunctor (Ab T) 0).obj (integers T) ⟶
      ((DerivedCategory.singleFunctor (Ab T) 0).obj (units T))⟦(1 : ℤ)⟧) :
    IntegralBoundaryNormalization l R A φ c f := by
  constructor
  exact normalizedDerivedExtension_arrow (C := Ab T) (D := Systems T R)
    c.reduction.model
    (towerKummerComplex l c.kummer) (towerKummerShortExact l c.kummer)
    c.unitIso c.rootIso c.rootForget (integerGenerator T R c.reduction.forget)
    hc.1 hc.2.1 f

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
