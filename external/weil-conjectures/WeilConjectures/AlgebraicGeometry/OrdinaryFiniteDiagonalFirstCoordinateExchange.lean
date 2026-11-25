/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalTraceCoordinates
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteSingleUnitNormalization
/-!
# The first normalized coordinate exchange

Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 20000] SymmetricCategory.toBraidedCategory
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
  AlgebraicGeometry.ProjectiveSpace

attribute [local implicit_reducible] projectiveLineDiagonalProjection
attribute [local implicit_reducible] constantComplex constantSheaf
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
attribute [local implicit_reducible] sheafMonoidalCategory sheafBraidedCategory derivedTensorRight
attribute [local instance 21000] sheafBraidedCategory
attribute [local irreducible] derivedBaseChangeMap CoordinateTrace.exchange1
  CoordinateTrace.exchange2
  ordinaryFiniteShiftedLinePullback projectiveLineDiagonalAlpha
  singleFunctorObjUnitIso derivedTensorRightUnitor

/-- Normalize scalar chart exchange to the first common-base coordinate.
Source: blueprint thm-amb-p1-adjunction.proof.md, the coordinate trace calculations.
(auxiliary; not a blueprint node).
Proof: Specialize scalar chart exchange to the first projection and rewrite the canonical
single-object unit comparison through its typed cache. Associativity gives the first
coordinate exchange equation. -/
theorem ordinaryFiniteDiagonalTrace_first_coordinate_exchange (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (c : OrdinaryFiniteP1ChernFamily A N hA)
    (b : ∀ (S : Scheme.{u}) [IsNoetherian S] (_hS : IsUnit (N : Γ(S, ⊤))),
      ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ≅
        (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧))
    (hb : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
      (b S hS).hom = ordinaryFiniteP1KummerMap A N hA t c S hS)
    (hbc : OrdinaryFiniteP1KummerMapBaseChange A N hA t c)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
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
    let τ := (b S hS).inv ≫ biprod.snd
    let τP := (b P hP).inv ≫ biprod.snd
    let t₀ := (ordinaryFinitePushforward A q).map w.hom ≫ τ ≫
      (ordinaryFiniteSingleUnitIso A S).hom
    let t₁ := (ordinaryFinitePushforward A (pullback.fst q q)).map w₂.hom ≫
      ordinaryFiniteP1DiagonalChartMap A N hA t S hS false ≫ τP ≫
        (ordinaryFiniteSingleUnitIso A P).hom
    (CoordinateTrace.exchange1 A q
      ((ordinaryFinitePullback A q).obj L)).hom ≫ t₁ =
        (ordinaryFinitePullback A q).map t₀ ≫
          (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) q).hom := by
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
  let τ := (b S hS).inv ≫ biprod.snd
  let τP := (b P hP).inv ≫ biprod.snd
  let t₀ := (ordinaryFinitePushforward A q).map w.hom ≫ τ ≫
    (ordinaryFiniteSingleUnitIso A S).hom
  let t₁ := (ordinaryFinitePushforward A (pullback.fst q q)).map w₂.hom ≫
    ordinaryFiniteP1DiagonalChartMap A N hA t S hS false ≫ τP ≫
      (ordinaryFiniteSingleUnitIso A P).hom
  have ht₁ : (CoordinateTrace.exchange1 A q
      ((ordinaryFinitePullback A q).obj L)).hom ≫ t₁ =
        (ordinaryFinitePullback A q).map t₀ ≫
          (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) q).hom := by
    as_aux_lemma =>
      have hh := ordinaryFiniteDiagonalTrace_exchange N hN A hA t c b hb hbc S hS false
      dsimp only [projectiveLineDiagonalSquare, Bool.not,
        projectiveLineDiagonalProjection] at hh
      dsimp only [t₁, t₀, τP, τ, w₂, w, L, q, P]
      rw [← ordinaryFiniteSingleUnitIso_eq A (ProjectiveLine S),
        ← ordinaryFiniteSingleUnitIso_eq A S] at hh
      rw [ordinaryFiniteSingleUnit_assoc A (ProjectiveLine S),
        ordinaryFiniteSingleUnit_assoc A S]
      simpa only [t₁, t₀, τP, τ, w₂, w, L, q, P, hP, Bool.not_false,
        projectiveLineDiagonalProjection, CoordinateTrace.exchange1, asIso_hom,
        Category.assoc] using hh
  exact ht₁

end AlgebraicGeometry.Etale
