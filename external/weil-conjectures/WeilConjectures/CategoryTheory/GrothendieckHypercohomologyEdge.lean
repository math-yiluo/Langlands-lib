/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.HypercohomologyLeftEdge
public import WeilConjectures.CategoryTheory.GrothendieckComposablePair

import WeilConjectures.CategoryTheory.GrothendieckResolutionUnitComparison

/-! # Comparing the resolution and complex hypercohomology edges

Source: Stacks Project, derived.tex, Tags 015N and 015J.
(blueprint: lem-pc-grothendieck-hypercohomology-edge).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private lemma pageTargetComparison
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] (X : A) (n : ℕ)
    (m : ℤ) (hm : m = (0 : ℤ) + n) :
    (F.grothendieckSpectralObjectHIso G 0 n m n (n + 1) hm rfl rfl).hom.app X =
      (DerivedCategory.Plus.homologyFunctor C m).map (G.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.eTruncLTCompETruncGEIso (n : ℤ)).hom.app
          (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)))) ≫
      (DerivedCategory.Plus.homologyFunctor C m).map (G.rightDerivedFunctorPlus.map
        (((DerivedCategory.Plus.singleFunctors B).shiftIso (-(n : ℤ)) n 0 (by simp)).inv.app
          ((DerivedCategory.Plus.homologyFunctor B n).obj
            (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))))) ≫
      (DerivedCategory.Plus.homologyFunctor C m).map
        ((G.rightDerivedFunctorPlus.commShiftIso (-(n : ℤ))).hom.app
          ((DerivedCategory.Plus.singleFunctor B 0).obj
            ((DerivedCategory.Plus.homologyFunctor B n).obj
              (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))))) ≫
      ((DerivedCategory.Plus.homologyFunctor C 0).shiftIso (-(n : ℤ)) m 0 (by omega)).hom.app
          (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj
            ((DerivedCategory.Plus.homologyFunctor B n).obj
              (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))))) ≫
      (G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).hom.app
        ((DerivedCategory.Plus.homologyFunctor B n).obj
          (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))) ≫
      (G.rightDerived 0).map
        ((F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n).hom.app X) := by
  subst hm
  simp only [Functor.grothendieckSpectralObjectHIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.comp_map]
  rfl

private lemma grothendieckLeftEdgeTargetIso_hom_app
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] (X : A) (n : ℕ) :
    (F.grothendieckLeftEdgeTargetIso G n).hom.app X =
      (G.hypercohomologyLeftEdgeTargetIso n).hom.app
          (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)) ≫
        G.map (F.homologyRightDerivedFunctorPlusObjSingleFunctorIso X n).hom := by
  simp only [Functor.grothendieckLeftEdgeTargetIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  rw [pageTargetComparison F G X n n (by simp)]
  simp only [Functor.hypercohomologyLeftEdgeTargetIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.comp_map, Category.assoc]
  rw [G.rightDerivedZeroIsoSelf.hom.naturality]
  rfl

/-- For F applied to an injective resolution, the Grothendieck edge is the
hypercohomology edge transported through the canonical resolution comparisons.
Source: Stacks Project, Tags 015N and 015J; steps 1 and 2 of
lem-pc-grothendieck-cocycle-comparison
(blueprint: lem-pc-grothendieck-hypercohomology-edge).

Proof:
The prescribed resolution comparison identifies RF(X[0]) with Q of the zero
extension of F(I), and intertwines the composite-derived homology comparison
with the G-derived unit. Transport the truncation spectral object through this
isomorphism. Naturality of its left edge identifies the transported edge map.
The canonical target comparison factors into the complex target comparison and
G of H^n(RF(X[0])) -> R^nF(X); this follows by expanding the truncation/shift
factors and using naturality of rightDerivedZeroIsoSelf. The ordinary resolution
comparison replaces the latter factor by G of H^n(F(I)). Substitute these source
and target equations, and associate the composites. The resulting expression
is the definition of cochainHypercohomologyLeftEdge, in every degree including
zero. No double-complex presentation or filtration model is required.
-/
theorem grothendieckLeftEdgeMap_eq_hypercohomology
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics)
    (X : A) (I : InjectiveResolution X) (n : ℕ) :
    (I.isoRightDerivedObj (F ⋙ G) n).inv ≫
        (F.grothendieckLeftEdgeMap G hFG n).app X ≫
        G.map (I.isoRightDerivedObj F n).hom =
      G.cochainHypercohomologyLeftEdge
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) n := by
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let L : CochainComplex.Plus B := ⟨K.extend ComplexShape.embeddingUpNat, 0,
    inferInstance⟩
  have : DerivedCategory.Plus.TStructure.t.IsGE (DerivedCategory.Plus.Q.obj L) 0 := by
    apply (DerivedCategory.Plus.isGE_ι_obj_iff _ 0).mp
    exact inferInstanceAs ((DerivedCategory.Q.obj L.obj).IsGE 0)
  obtain ⟨e, hF, hFG'⟩ := exists_grothendieck_resolution_unit_comparison F G hFG X I n
  let φ := G.hypercohomologySpectralObjectFunctor.map e.hom
  have hnat := Abelian.SpectralObject.leftEdge_naturality φ (n : ℤ)
  have ht := (G.hypercohomologyLeftEdgeTargetIso n).hom.naturality e.hom
  have ht' :
      (F.grothendieckLeftEdgeTargetIso G n).hom.app X ≫
          G.map (I.isoRightDerivedObj F n).hom =
        (φ.hom (n : ℤ)).app _ ≫
          (G.hypercohomologyLeftEdgeTargetIso n).hom.app (DerivedCategory.Plus.Q.obj L) ≫
          G.map ((DerivedCategory.Plus.homologyFunctorObjQIso L n).hom ≫
            (K.extendHomologyIso ComplexShape.embeddingUpNat
              (rfl : (n : ℤ) = n)).hom) := by
    rw [grothendieckLeftEdgeTargetIso_hom_app, Category.assoc, ← G.map_comp, hF,
      G.map_comp]
    simpa only [Functor.comp_map, Abelian.SpectralObject.hFunctor, Category.assoc] using
      congrArg (· ≫ G.map ((DerivedCategory.Plus.homologyFunctorObjQIso L n).hom ≫
      (K.extendHomologyIso ComplexShape.embeddingUpNat
        (rfl : (n : ℤ) = n)).hom)) ht.symm
  simp only [Functor.grothendieckLeftEdgeMap, NatTrans.comp_app, Category.assoc]
  rw [ht']
  change _ ≫ _ ≫
    (G.hypercohomologySpectralObjectFunctor.obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))).leftEdge
      (n : ℤ) ≫ _ = _
  rw [← reassoc_of% hnat]
  change (I.isoRightDerivedObj (F ⋙ G) n).inv ≫
      (F.grothendieckSpectralObjectHBotTopIso G hFG n).inv.app X ≫
      (DerivedCategory.Plus.homologyFunctor C n).map
        (G.rightDerivedFunctorPlus.map e.hom) ≫ _ = _
  rw [reassoc_of% hFG']
  rfl

end CategoryTheory
