/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
import WeilConjectures.AlgebraicGeometry.EtaleDiagonalCoefficientTriangles
import WeilConjectures.AlgebraicGeometry.EtaleSectionUnitNormalization
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalFirstCoordinateExchange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalSecondCoordinateExchange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalIntegral
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# The supported diagonal unit and its two triangles

Source: blueprint thm-amb-p1-adjunction.proof.md.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
private theorem mapIsoIntegral
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {U V W : C} (e : V ≅ W) (k : U ⟶ W)
    {P Q : D} (a : P ⟶ F.obj U) (b : F.obj W ⟶ Q) :
    a ≫ F.map (k ≫ e.inv) ≫ F.map e.hom ≫ b = a ≫ F.map k ≫ b := by
  rw [← Functor.map_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

attribute [local implicit_reducible] ordinaryFiniteP1Right in
private theorem p1TriangleSpecialization
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S]
    (b : ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ≅
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) :
    let q := ProjectiveLine S ↘ S
    let L := (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧
    let : IsLocallyNoetherian (ProjectiveLine S) :=
      LocallyOfFiniteType.isLocallyNoetherian q
    let : CompactSpace (ProjectiveLine S) := QuasiCompact.compactSpace_of_compactSpace q
    (∃ η : 𝟭 (DerivedCategoryModule A (ProjectiveLine S)) ⟶
        ordinaryFinitePushforward A q ⋙ ordinaryFiniteTwistedPullback A q L,
      (∀ M, (ordinaryFinitePushforward A q).map (η.app M) ≫
        (ordinaryFiniteTraceCounit A q L (b.inv ≫ biprod.snd)).app
          ((ordinaryFinitePushforward A q).obj M) = 𝟙 _) ∧
      (∀ K, η.app ((ordinaryFiniteTwistedPullback A q L).obj K) ≫
        (ordinaryFiniteTwistedPullback A q L).map
          ((ordinaryFiniteTraceCounit A q L (b.inv ≫ biprod.snd)).app K) = 𝟙 _)) →
    (∃ η : 𝟭 (DerivedCategoryModule A (ProjectiveLine S)) ⟶
        ordinaryFinitePushforward A q ⋙ ordinaryFiniteP1Right A N hA S,
      (∀ M, (ordinaryFinitePushforward A q).map (η.app M) ≫
        (ordinaryFiniteP1TraceCounit A N hA S b).app
          ((ordinaryFinitePushforward A q).obj M) = 𝟙 _) ∧
      (∀ K, η.app ((ordinaryFiniteP1Right A N hA S).obj K) ≫
        (ordinaryFiniteP1Right A N hA S).map
          ((ordinaryFiniteP1TraceCounit A N hA S b).app K) = 𝟙 _)) := by
  dsimp only
  intro h
  unfold ordinaryFiniteP1TraceCounit ordinaryFiniteP1Right
  exact h

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 20000] SymmetricCategory.toBraidedCategory
attribute [local implicit_reducible] projectiveLineDiagonalProjection
attribute [local implicit_reducible] constantComplex constantSheaf
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
attribute [local implicit_reducible] sheafMonoidalCategory sheafBraidedCategory derivedTensorRight
  ordinaryFiniteP1Right ordinaryFiniteTwistedPullback
attribute [local instance 21000] sheafBraidedCategory
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
  derivedBaseChangeMap CoordinateTrace.exchange1 CoordinateTrace.exchange2
  ordinaryFiniteShiftedLinePullback projectiveLineDiagonalAlpha
  singleFunctorObjUnitIso derivedTensorRightUnitor

private theorem finiteLine_lisse
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    Scheme.IsLisseRankOneSheaf (Scheme.finiteEtaleTateLine S N A hA) := by
  obtain ⟨cover, hc⟩ := (Scheme.finiteEtaleTwistPullbackData A N hN hA).laws.1 S hS
  refine ⟨cover, fun i ↦ ?_⟩
  obtain ⟨e⟩ := hc i 1
  let U := cover.etalePrecoverageToEtale i
  let E := Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} A)
  let c := (Scheme.Etale.overEquiv U).constantSheafSheafCongrIso
    (S.smallEtaleTopology.over U) U.left.smallEtaleTopology (ModuleCat.{u + 1} A)
    Over.mkIdTerminal
  exact ⟨(Scheme.overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} A) U
    (Scheme.finiteEtaleTateLine S N A hA)).symm ≪≫ E.functor.mapIso e ≪≫
      c.app (ModuleCat.of A A)⟩

theorem ordinaryFiniteP1_diagonal_triangles (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (c : OrdinaryFiniteP1ChernFamily A N hA)
    (hc : OrdinaryFiniteP1ChernFamilySpec A N hA c)
    (b : ∀ (S : Scheme.{u}) [IsNoetherian S] (_hS : IsUnit (N : Γ(S, ⊤))),
      ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ≅
        (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧))
    (hb : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
      (b S hS).hom = ordinaryFiniteP1KummerMap A N hA t c S hS)
    (hbc : OrdinaryFiniteP1KummerMapBaseChange A N hA t c) :
    (∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
      ∃ η : 𝟭 (DerivedCategoryModule A (ProjectiveLine S)) ⟶
          ordinaryFinitePushforward A (ProjectiveLine S ↘ S) ⋙
            ordinaryFiniteP1Right A N hA S,
        (∀ M : DerivedCategoryModule A (ProjectiveLine S),
          (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map (η.app M) ≫
            (ordinaryFiniteP1TraceCounit A N hA S (b S hS)).app
              ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj M) = 𝟙 _) ∧
        (∀ K : DerivedCategoryModule A S,
          η.app ((ordinaryFiniteP1Right A N hA S).obj K) ≫
            (ordinaryFiniteP1Right A N hA S).map
              ((ordinaryFiniteP1TraceCounit A N hA S (b S hS)).app K) = 𝟙 _)) := by
  intro S _ hS
  classical
  let P := ProjectiveLine S
  let q := ProjectiveLine S ↘ S
  let : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  let : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace q
  let : IsNoetherian P := ⟨⟩
  let hP := affineTraceProjectiveInvertible N S hS
  let L := (ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧
  let w := ordinaryFiniteShiftedLinePullback A N hA t q hS
  let w₂ : (ordinaryFinitePullback A (pullback.snd q q)).obj
      ((ordinaryFinitePullback A q).obj L) ≅
        (ordinaryFiniteLine A N hA (pullback q q))⟦(2 : ℤ)⟧ :=
    ordinaryFiniteDiagonalCoefficientIso A N hA t S hS true
  obtain ⟨hI, κ, hκ, hi⟩ := ordinaryFiniteP1_diagonal_integral
    N A hA t c b hb hN hc S hS
  let δ : (ordinaryFinitePushforward A (pullback.diagonal q)).obj
      (ordinaryFiniteUnit A P) ⟶
        (ordinaryFinitePullback A (pullback.snd q q)).obj
          ((ordinaryFinitePullback A q).obj L) :=
    ordinaryFiniteSupportedRealization A (pullback.diagonal q)
    (Scheme.finiteEtaleTateLine (pullback q q) N A hA) κ ≫ w₂.inv
  let τ := (b S hS).inv ≫ biprod.snd
  let τP := (b P hP).inv ≫ biprod.snd
  let t₀ := (ordinaryFinitePushforward A q).map w.hom ≫ τ ≫
    (ordinaryFiniteSingleUnitIso A S).hom
  let t₁ := (ordinaryFinitePushforward A (pullback.fst q q)).map w₂.hom ≫
    ordinaryFiniteP1DiagonalChartMap A N hA t S hS false ≫ τP ≫
      (ordinaryFiniteSingleUnitIso A P).hom
  let t₂ := (ordinaryFinitePushforward A (pullback.snd q q)).map w₂.hom ≫
    ordinaryFiniteP1DiagonalChartMap A N hA t S hS true ≫ τP ≫
      (ordinaryFiniteSingleUnitIso A P).hom
  have ht₁ := ordinaryFiniteDiagonalTrace_first_coordinate_exchange
    N hN A hA t c b hb hbc S hS
  have ht₂ := ordinaryFiniteDiagonalTrace_second_coordinate_exchange
    N hN A hA t c b hb hbc S hS
  have hi₀ (a : Bool) : projectiveLineDiagonalAlpha A S a ≫
      (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map δ ≫
        (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map w₂.hom ≫
        ordinaryFiniteP1DiagonalChartMap A N hA t S hS a ≫ τP = 𝟙 _ := by
    dsimp only [δ, τP, hP, q, P]
    have hh := hi a
    unfold ordinaryFiniteP1DiagonalSupportedMap at hh
    apply (mapIsoIntegral
      (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a))
      (U := (ordinaryFinitePushforward A (pullback.diagonal q)).obj
        (ordinaryFiniteUnit A P))
      w₂ (ordinaryFiniteSupportedRealization A (pullback.diagonal q)
        (Scheme.finiteEtaleTateLine (pullback q q) N A hA) κ)
      (projectiveLineDiagonalAlpha A S a)
      (ordinaryFiniteP1DiagonalChartMap A N hA t S hS a ≫
        (b (ProjectiveLine S) (affineTraceProjectiveInvertible N S hS)).inv ≫ biprod.snd)).trans
    simpa only [Category.assoc, q, P] using hh
  have hi₂ : (diagonalPushSection A q).hom.app (ordinaryFiniteUnit A P) ≫
      (ordinaryFinitePushforward A (pullback.snd q q)).map δ ≫ t₂ ≫
        (ordinaryFiniteSingleUnitIso A P).inv = 𝟙 _ := by
    as_aux_lemma =>
      have hh := hi₀ true
      rw [projectiveLineDiagonalAlpha_eq] at hh
      dsimp only [t₂, q, P, projectiveLineDiagonalProjection, diagonalPushSection]
      simp only [Category.assoc]
      erw [Iso.hom_inv_id (ordinaryFiniteSingleUnitIso A (ProjectiveLine S)), Category.comp_id]
      simpa only [q, P, projectiveLineDiagonalProjection, Category.assoc,
        diagonalPushSection, Functor.id_obj] using hh
  have hi₁ : (diagonalFirstPushSection A q).hom.app (ordinaryFiniteUnit A P) ≫
      (ordinaryFinitePushforward A (pullback.fst q q)).map δ ≫ t₁ ≫
        (ordinaryFiniteSingleUnitIso A P).inv = 𝟙 _ := by
    as_aux_lemma =>
      have hh := hi₀ false
      rw [projectiveLineDiagonalAlpha_eq] at hh
      dsimp only [t₁, q, P, projectiveLineDiagonalProjection, diagonalFirstPushSection]
      simp only [Category.assoc]
      erw [Iso.hom_inv_id (ordinaryFiniteSingleUnitIso A (ProjectiveLine S)), Category.comp_id]
      simpa only [q, P, projectiveLineDiagonalProjection, Category.assoc,
        diagonalFirstPushSection, Functor.id_obj] using hh
  apply p1TriangleSpecialization A N hA S (b S hS)
  exact evenLineDiagonalUnit_triangles A q (Scheme.finiteEtaleTateLine S N A hA)
    (finiteLine_lisse N hN A hA S hS) 1 _ w τ t₀ rfl δ t₁ t₂ ht₁ ht₂ hi₁ hi₂
end AlgebraicGeometry.Etale
