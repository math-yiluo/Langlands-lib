/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSupportedDiagonalUnit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.EtaleProperSectionContraction
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# The triangle identities from the two diagonal integrals -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local implicit_reducible] derivedTensorRight CoordinateTrace.H constantComplex
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
  conjugateIsoEquiv conjugateEquiv Adjunction.comp
  leftDerivedUpperStarCompSectionIso leftDerivedUpperStarComp
  derivedUpperStarLowerStarAdjunction
attribute [local instance 20000] SymmetricCategory.toBraidedCategory

private theorem second_triangle_calculation
    {C E : Type*} [Category C] [Category E] (Q : E ⥤ C)
    {M U : C} {V₀ V₁ V₀' V₂ W : E}
    (a : M ⟶ Q.obj W) (d : W ⟶ V₀) (d' : W ⟶ V₀')
    (x : V₀ ⟶ V₁) (x' : V₀' ⟶ V₂) (b : V₁ ⟶ V₂) (t : V₀ ⟶ V₀')
    (c c' : Q.obj V₁ ⟶ U) (e : U ⟶ M) (r : Q.obj V₂ ⟶ M)
    (hc : c' = c) (he : c ≫ e = Q.map b ≫ r) (hn : x ≫ b = t ≫ x')
    (hd : d ≫ t = d') (ht : a ≫ Q.map d' ≫ Q.map x' ≫ r = 𝟙 M) :
    (a ≫ Q.map d ≫ Q.map x ≫ c') ≫ e = 𝟙 M := by
  rw [hc]
  simp only [Category.assoc]
  calc
    _ = a ≫ Q.map d ≫ Q.map x ≫ Q.map b ≫ r := by rw [he]
    _ = a ≫ Q.map (d ≫ (x ≫ b)) ≫ r := by
      simp only [Functor.map_comp, Category.assoc]
    _ = a ≫ Q.map ((d ≫ t) ≫ x') ≫ r := by rw [hn, Category.assoc]
    _ = a ≫ Q.map d' ≫ Q.map x' ≫ r := by
      rw [hd, Functor.map_comp, Category.assoc]
    _ = 𝟙 M := ht

private theorem first_triangle_components
    {C D E : Type*} [Category C] [Category D] [Category E]
    (P : C ⥤ D) (R R₁ : E ⥤ C) {M U : C} {V₀ V₁ V₂ : E}
    (a : M ⟶ R.obj V₀) (q : V₀ ⟶ V₁) (d : V₁ ⟶ V₂)
    (c : R.obj V₂ ⟶ U) (ε : P.obj U ⟶ P.obj M)
    (comp : P.obj (R.obj V₂) ⟶ P.obj (R₁.obj V₂))
    (r : R₁.obj V₂ ⟶ M) (a₁ : M ⟶ R₁.obj V₀)
    (he : P.map c ≫ ε = comp ≫ P.map r)
    (hn : P.map (a ≫ R.map (q ≫ d)) ≫ comp = P.map (a₁ ≫ R₁.map (q ≫ d)))
    (hi : a₁ ≫ R₁.map (q ≫ d) ≫ r = 𝟙 M) :
    P.map (a ≫ R.map q ≫ R.map d ≫ c) ≫ ε = 𝟙 (P.obj M) := by
  calc
    _ = P.map (a ≫ R.map (q ≫ d)) ≫ (P.map c ≫ ε) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (P.map (a ≫ R.map (q ≫ d)) ≫ comp) ≫ P.map r := by
      rw [he, Category.assoc]
    _ = P.map (a₁ ≫ R₁.map (q ≫ d)) ≫ P.map r := by rw [hn]
    _ = P.map (a₁ ≫ R₁.map (q ≫ d) ≫ r) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = 𝟙 _ := by rw [hi, P.map_id]

private theorem coordinateDirectComparison_eq
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CoordinateTrace.directComparison A f =
      derivedDirectCoordinateIso (ModuleCat.{u + 1} A) f := by
  rfl

private theorem diagonalSection_push_naturality_cached
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategoryModule A X) {V : DerivedCategoryModule A (pullback f f)}
    (d : (ordinaryFinitePushforward A (pullback.diagonal f)).obj M ⟶ V) :
    (CoordinateTrace.push A f).map
        ((diagonalPushSection A f).hom.app M ≫
          (CoordinateTrace.push A (pullback.snd f f)).map d) ≫
      (CoordinateTrace.directComparison A f).hom.app V =
    (CoordinateTrace.push A f).map
      ((diagonalFirstPushSection A f).hom.app M ≫
        (CoordinateTrace.push A (pullback.fst f f)).map d) := by
  rw [coordinateDirectComparison_eq]
  exact diagonalSection_push_naturality (ModuleCat.{u + 1} A) f M d

/-- The first triangle is the first section integral after coordinate interchange. -/
theorem supportedDiagonalUnit_first
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (L : DerivedCategoryModule A Y)
    (δ : (ordinaryFinitePushforward A (pullback.diagonal f)).obj (ordinaryFiniteUnit A X) ⟶
      (ordinaryFinitePullback A (pullback.snd f f)).obj
        ((ordinaryFinitePullback A f).obj L))
    (t : (CoordinateTrace.push A f).obj ((CoordinateTrace.pull A f).obj L) ⟶
      constantComplex A Y)
    (t₁ : (CoordinateTrace.push A (pullback.fst f f)).obj
      ((CoordinateTrace.pull A (pullback.snd f f)).obj ((CoordinateTrace.pull A f).obj L)) ⟶
      constantComplex A X)
    (he : ∀ M : DerivedCategoryModule A X,
      (CoordinateTrace.push A f).map (CoordinateTrace.comparison A f L M).hom ≫
          CoordinateTrace.evaluation A f L t ((CoordinateTrace.push A f).obj M) =
        (CoordinateTrace.directComparison A f).hom.app _ ≫
          (CoordinateTrace.push A f).map
            ((CoordinateTrace.orderedProjectionIso A (pullback.fst f f) M
              ((CoordinateTrace.pull A (pullback.snd f f)).obj
                ((CoordinateTrace.pull A f).obj L))).inv ≫
              ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map t₁ ≫
                (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X M).hom))
    (hi : ∀ M : DerivedCategoryModule A X,
      let a₁ := diagonalFirstPushSection A f
      a₁.hom.app M ≫
          (ordinaryFinitePushforward A (pullback.fst f f)).map
            ((diagonalTensorIso A f).inv.app M ≫
              ((ordinaryFiniteTensor A (pullback f f)).obj
                ((ordinaryFinitePullback A (pullback.fst f f)).obj M)).map δ) ≫
          (CoordinateTrace.orderedProjectionIso A (pullback.fst f f) M
            ((CoordinateTrace.pull A (pullback.snd f f)).obj
              ((CoordinateTrace.pull A f).obj L))).inv ≫
          ((ordinaryFiniteTensor A X).obj M).map t₁ ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X M).hom = 𝟙 M)
    (M : DerivedCategoryModule A X) :
    (ordinaryFinitePushforward A f).map
        (Adjunction.unitComponent (ordinaryFinitePushforward A f) (CoordinateTrace.H A f L)
          (supportedDiagonalUnit A f L δ) M) ≫
      CoordinateTrace.evaluation A f L t ((ordinaryFinitePushforward A f).obj M) =
        𝟙 ((ordinaryFinitePushforward A f).obj M) := by
  apply Eq.trans (supportedDiagonalUnit_map_post_app A f L δ M
    (ordinaryFinitePushforward A f)
    (CoordinateTrace.evaluation A f L t ((ordinaryFinitePushforward A f).obj M)))
  rw [diagonalComparison_hom_app]
  refine first_triangle_components
    (V₂ := CoordinateTrace.tensor A (pullback f f)
      ((CoordinateTrace.pull A (pullback.fst f f)).obj M)
      ((CoordinateTrace.pull A (pullback.snd f f)).obj ((CoordinateTrace.pull A f).obj L)))
    (CoordinateTrace.push A f)
    (CoordinateTrace.push A (pullback.snd f f))
    (CoordinateTrace.push A (pullback.fst f f))
    ((diagonalPushSection A f).hom.app M)
    ((diagonalTensorIso A f).inv.app M)
    (((ordinaryFiniteTensor A (pullback f f)).obj
      ((ordinaryFinitePullback A (pullback.fst f f)).obj M)).map δ)
    (CoordinateTrace.comparison A f L M).hom
    (CoordinateTrace.evaluation A f L t ((ordinaryFinitePushforward A f).obj M))
    ((CoordinateTrace.directComparison A f).hom.app _)
    ((CoordinateTrace.orderedProjectionIso A (pullback.fst f f) M
      ((CoordinateTrace.pull A (pullback.snd f f)).obj
        ((CoordinateTrace.pull A f).obj L))).inv ≫
      ((ordinaryFiniteTensor A X).obj M).map t₁ ≫
        (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X M).hom)
    ((diagonalFirstPushSection A f).hom.app M) ?_ ?_ ?_
  · as_aux_lemma =>
      simpa only [ordinaryFiniteTensor, CoordinateTrace.push, ordinaryFinitePushforward,
        constantComplex, Functor.id_obj] using he M
  · as_aux_lemma =>
      exact diagonalSection_push_naturality_cached A f M
        (V := CoordinateTrace.tensor A (pullback f f)
          ((CoordinateTrace.pull A (pullback.fst f f)).obj M)
          ((CoordinateTrace.pull A (pullback.snd f f)).obj ((CoordinateTrace.pull A f).obj L)))
        ((diagonalTensorIso A f).inv.app M ≫
        ((ordinaryFiniteTensor A (pullback f f)).obj
          ((ordinaryFinitePullback A (pullback.fst f f)).obj M)).map δ)
  · as_aux_lemma =>
      exact hi M

/-- Coordinate interchange cancels against the two section projections. -/
theorem diagonalTensorMap_coordinate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (M : DerivedCategoryModule A X)
    (c : (ordinaryFinitePullback A (pullback.fst f f)).obj M ⟶
      (ordinaryFinitePullback A (pullback.snd f f)).obj M)
    (hc : (ordinaryFinitePullback A (pullback.diagonal f)).map c ≫
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) (pullback.diagonal f)
        (pullback.snd f f) (pullback.diagonal_snd f)).hom.app M =
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) (pullback.diagonal f)
        (pullback.fst f f) (pullback.diagonal_fst f)).hom.app M) :
    let q₂ := (CoordinateTrace.orderedProjectionIso A (pullback.diagonal f)
      ((ordinaryFinitePullback A (pullback.snd f f)).obj M)
      (ordinaryFiniteUnit A X)).hom ≫
      (ordinaryFinitePushforward A (pullback.diagonal f)).map
        (((ordinaryFiniteTensor A X).map
          ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) (pullback.diagonal f)
            (pullback.snd f f) (pullback.diagonal_snd f)).hom.app M)).app
              (ordinaryFiniteUnit A X) ≫ (singleUnitor A X).hom.app M)
    (((ordinaryFiniteTensor A (pullback f f)).map c).app
        ((ordinaryFinitePushforward A (pullback.diagonal f)).obj (ordinaryFiniteUnit A X))) ≫
      q₂ = (diagonalTensorIso A f).hom.app M := by
  intro q₂
  have hn := ordinaryFiniteProjection_naturality A (pullback.diagonal f)
    (ordinaryFiniteUnit A X) c
  change _ ≫ (CoordinateTrace.orderedProjectionIso A (pullback.diagonal f)
      ((ordinaryFinitePullback A (pullback.snd f f)).obj M)
      (ordinaryFiniteUnit A X)).hom =
    (CoordinateTrace.orderedProjectionIso A (pullback.diagonal f)
      ((ordinaryFinitePullback A (pullback.fst f f)).obj M)
      (ordinaryFiniteUnit A X)).hom ≫ _ at hn
  dsimp only [q₂]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
  rw [← Category.assoc]
  rw [← NatTrans.comp_app, ← Functor.map_comp, hc]
  rfl

/-- The second triangle is the second section integral. -/
theorem supportedDiagonalUnit_second
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (L : DerivedCategoryModule A Y)
    (δ : (ordinaryFinitePushforward A (pullback.diagonal f)).obj (ordinaryFiniteUnit A X) ⟶
      (ordinaryFinitePullback A (pullback.snd f f)).obj
        ((ordinaryFinitePullback A f).obj L))
    (t : (CoordinateTrace.push A f).obj ((CoordinateTrace.pull A f).obj L) ⟶
      constantComplex A Y)
    (t₂ : (CoordinateTrace.push A (pullback.snd f f)).obj
      ((CoordinateTrace.pull A (pullback.snd f f)).obj ((CoordinateTrace.pull A f).obj L)) ⟶
      constantComplex A X)
    (he : ∀ K : DerivedCategoryModule A Y,
      (CoordinateTrace.comparison A f L ((CoordinateTrace.H A f L).obj K)).hom ≫
          (CoordinateTrace.H A f L).map (CoordinateTrace.evaluation A f L t K) =
        (ordinaryFinitePushforward A (pullback.snd f f)).map
          (((ordinaryFiniteTensor A (pullback f f)).map
            (CoordinateTrace.coordinateH A f L K).hom).app
              ((ordinaryFinitePullback A (pullback.snd f f)).obj
                ((ordinaryFinitePullback A f).obj L))) ≫
          (CoordinateTrace.orderedProjectionIso A (pullback.snd f f)
            ((CoordinateTrace.H A f L).obj K)
            ((ordinaryFinitePullback A (pullback.snd f f)).obj
              ((ordinaryFinitePullback A f).obj L))).inv ≫
          ((ordinaryFiniteTensor A X).obj ((CoordinateTrace.H A f L).obj K)).map t₂ ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X
            ((CoordinateTrace.H A f L).obj K)).hom)
    (hi : (diagonalPushSection A f).hom.app (ordinaryFiniteUnit A X) ≫
      (ordinaryFinitePushforward A (pullback.snd f f)).map δ ≫ t₂ ≫
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X).inv = 𝟙 _) :
    ∀ K : DerivedCategoryModule A Y,
      Adjunction.unitComponent (ordinaryFinitePushforward A f) (CoordinateTrace.H A f L)
          (supportedDiagonalUnit A f L δ) ((CoordinateTrace.H A f L).obj K) ≫
        (CoordinateTrace.H A f L).map (CoordinateTrace.evaluation A f L t K) = 𝟙 _ := by
  intro K
  rw [Adjunction.unitComponent_eq]
  let M := (CoordinateTrace.H A f L).obj K
  let p₂ := pullback.snd f f
  let i := pullback.diagonal f
  let l₂ := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) i p₂
    (pullback.diagonal_snd f)
  let q₂ := CoordinateTrace.orderedProjectionIso A i
    ((ordinaryFinitePullback A p₂).obj M) (ordinaryFiniteUnit A X) ≪≫
      (ordinaryFinitePushforward A i).mapIso
        (((ordinaryFiniteTensor A X).mapIso (l₂.app M)).app
          (ordinaryFiniteUnit A X) ≪≫ (singleUnitor A X).app M)
  have hq := diagonalTensorMap_coordinate A f M (CoordinateTrace.coordinateH A f L K).hom
    (diagonalCoordinateTransport
      (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f f)).leftDerivedFunctor
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd f f)).leftDerivedFunctor
      (upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) i (pullback.fst f f)
        (pullback.diagonal_fst f)) l₂
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (CommSq.mk (pullback.condition (f := f) (g := f)).symm)).hom
      (((ordinaryFiniteTensor A Y).obj K).obj L)
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f K L)
      (diagonalSection_coordinate (ModuleCat.{u + 1} A) f _))
  change _ ≫ q₂.hom = (diagonalTensorIso A f).hom.app M at hq
  have hqi : (diagonalTensorIso A f).inv.app M ≫
      (((ordinaryFiniteTensor A (pullback f f)).map
        (CoordinateTrace.coordinateH A f L K).hom).app
          ((ordinaryFinitePushforward A i).obj (ordinaryFiniteUnit A X))) = q₂.inv := by
    apply (cancel_mono q₂.hom).mp
    rw [Category.assoc, hq, Iso.inv_hom_id_app, Iso.inv_hom_id]
  have hn := (((ordinaryFiniteTensor A (pullback f f)).map
      (CoordinateTrace.coordinateH A f L K).hom).naturality δ)
  have hi' : (diagonalPushSection A f).hom.app (ordinaryFiniteUnit A X) ≫
      (ordinaryFinitePushforward A p₂).map δ ≫
        (t₂ ≫ (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X).inv) = 𝟙 _ := hi
  have ht := properSection_contraction A (Y := pullback f f) i p₂ (pullback.diagonal_snd f) M
    ((ordinaryFinitePullback A p₂).obj ((ordinaryFinitePullback A f).obj L)) δ
    (t₂ ≫ (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X).inv) hi'
  change (diagonalPushSection A f).hom.app M ≫
    (ordinaryFinitePushforward A p₂).map q₂.inv ≫ _ = _ at ht
  apply Eq.trans (supportedDiagonalUnit_post_app A f L δ M
    ((CoordinateTrace.H A f L).map (CoordinateTrace.evaluation A f L t K)))
  apply second_triangle_calculation (M := M) (ordinaryFinitePushforward A p₂)
    ((diagonalPushSection A f).hom.app M)
    ((diagonalTensorIso A f).inv.app M) q₂.inv
    (((ordinaryFiniteTensor A (pullback f f)).obj
      ((ordinaryFinitePullback A (pullback.fst f f)).obj M)).map δ)
    (((ordinaryFiniteTensor A (pullback f f)).obj
      ((ordinaryFinitePullback A p₂).obj M)).map δ)
    (((ordinaryFiniteTensor A (pullback f f)).map
      (CoordinateTrace.coordinateH A f L K).hom).app
        ((ordinaryFinitePullback A p₂).obj ((ordinaryFinitePullback A f).obj L)))
    (((ordinaryFiniteTensor A (pullback f f)).map
      (CoordinateTrace.coordinateH A f L K).hom).app
        ((ordinaryFinitePushforward A i).obj (ordinaryFiniteUnit A X)))
    (CoordinateTrace.comparison A f L M).hom
    ((diagonalComparison A f L).hom.app M)
    ((CoordinateTrace.H A f L).map (CoordinateTrace.evaluation A f L t K))
    ((CoordinateTrace.orderedProjectionIso A p₂ M
      ((ordinaryFinitePullback A p₂).obj ((ordinaryFinitePullback A f).obj L))).inv ≫
        ((ordinaryFiniteTensor A X).obj M).map t₂ ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X M).hom)
    (diagonalComparison_hom_app A f L M) (he K) hn hqi
  erw [singleUnitor_cancel] at ht
  simpa only [Functor.id_obj] using ht

end AlgebraicGeometry.Etale
