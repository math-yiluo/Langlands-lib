/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows

/-!
# Normalized ordinary finite projective-line duality data

Source: blueprint proposition-adjunction-projective-line--1, lemma-cohomology-projective-line-trace
and lemma-cohomology-projective-line-trace (auxiliary; not a blueprint node).

## Main definitions

* `OrdinaryFiniteP1CounitNormalization`: the prescribed actual counit equation.
* `ordinaryFiniteP1DecompositionSourceMap`: pullback of the ordered two summands.
* `OrdinaryFiniteP1Datum`: the normalized decomposition, trace and adjunction data.
* `OrdinaryFiniteP1Datum.trace`: projection onto the specified second summand.
* `OrdinaryFiniteP1BaseChange`: the decomposition, trace and counit squares.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- The actual counit equation with the specified ordered projection map and trace.
Naming this predicate keeps the normalized datum's dependent projections compact.
Source: blueprint lemma-cohomology-projective-line-trace and
proposition-adjunction-projective-line--1 (auxiliary; not a blueprint node). -/
def OrdinaryFiniteP1CounitNormalization (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u})
    (b : ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ≅
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧))
    (adj : (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)) ⊣
      ordinaryFiniteP1Right A N hA S) : Prop :=
  ∀ K : DerivedCategoryModule A S,
    ordinaryFiniteProjection A (ProjectiveLine S ↘ S)
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) K ≫
      adj.counit.app K =
    ((ordinaryFiniteTensor A S).obj K).map
        (b.inv ≫ biprod.snd) ≫ (derivedTensorSingleUnitIso K).hom

/-- The normalized projective-line decomposition and adjunction data. Every map in
this record is constrained: the Chern class by the actual scalar Kummer boundary,
the decomposition by its two components, and the adjunction by its actual counit.
Trace is always `decomposition.inv ≫ biprod.snd`, not an independent chosen map.
Source: blueprint lemma-cohomology-projective-line-trace, lemma-cohomology-projective-line-trace,
proposition-adjunction-projective-line--1 (auxiliary; not a blueprint node). -/
structure OrdinaryFiniteP1Datum (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) where
  invertible_on_projectiveLine : IsUnit (N : Γ(ProjectiveLine S, ⊤))
  chern : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
    (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧
  chern_spec : ordinaryFiniteP1ChernSpec A N hA S invertible_on_projectiveLine chern
  decomposition :
    ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ≅
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
  decomposition_hom : decomposition.hom = biprod.desc
    (ordinaryFiniteP1Unit A N hA t S hS) (ordinaryFiniteP1ChernPushforward A N hA S chern)
  trace_chern : ordinaryFiniteP1ChernPushforward A N hA S chern ≫
    decomposition.inv ≫ biprod.snd = 𝟙 (ordinaryFiniteUnit A S)
  adjunction :
    (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)) ⊣
      ordinaryFiniteP1Right A N hA S
  counit_normalization : OrdinaryFiniteP1CounitNormalization A N hA S
    decomposition adjunction

/-- The trace is projection onto the second summand of the specified decomposition.
Source: blueprint lemma-cohomology-projective-line-trace (auxiliary; not a blueprint node). -/
def OrdinaryFiniteP1Datum.trace {A : Type (u + 1)} [CommRing A] {N : ℕ}
    {hA : (N : A) = 0} {t : OrdinaryFiniteTwistTransport A N hA}
    {S : Scheme.{u}} {hS : IsUnit (N : Γ(S, ⊤))}
    (d : OrdinaryFiniteP1Datum A N hA t S hS) :
    (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ⟶ ordinaryFiniteUnit A S :=
  d.decomposition.inv ≫ biprod.snd

/-- The canonical comparison on the two summands of the decomposition under inverse image.
It is the biproduct map assembled from the images of its projections and the normalized
shifted-line and constant-object comparisons.
Source: blueprint lemma-cohomology-projective-line-trace, base-change assertion
(auxiliary; not a blueprint node). -/
def ordinaryFiniteP1DecompositionSourceMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) :
    (ordinaryFinitePullback A f).obj
        ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ⟶
      ((ordinaryFiniteLine A N hA S')⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S') :=
  biprod.lift
    ((ordinaryFinitePullback A f).map biprod.fst ≫
      (ordinaryFiniteShiftedLinePullback A N hA t f hS).hom)
    ((ordinaryFinitePullback A f).map biprod.snd ≫
      (ordinaryFiniteUnitPullback A f).hom)

/-- Base-change compatibility of the normalized decomposition, its trace, and the
actual adjunction counit, using the specified exchange and tensor comparisons.
Source: blueprint proposition-adjunction-projective-line--1, final paragraph
(auxiliary; not a blueprint node). -/
def OrdinaryFiniteP1BaseChange (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
      OrdinaryFiniteP1Datum A N hA t S hS) : Prop :=
  ∀ {S' S : Scheme.{u}} [IsNoetherian S'] [IsNoetherian S]
    (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤))),
    ((ordinaryFinitePullback A f).map
        (d S hS).decomposition.hom ≫
      ordinaryFiniteP1Exchange A f ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
        (ordinaryFiniteShiftedLinePullback A N hA t
          (X := ProjectiveLine S') (Y := ProjectiveLine S)
          (ProjectiveSpace.map (ULift.{u} (Fin 2)) f) (d S hS).invertible_on_projectiveLine).hom =
    ordinaryFiniteP1DecompositionSourceMap A N hA t f hS ≫
      (d S' hS').decomposition.hom) ∧
    ((ordinaryFinitePullback A f).map (d S hS).trace ≫
        (ordinaryFiniteUnitPullback A f).hom =
      ordinaryFiniteP1Exchange A f ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteShiftedLinePullback A N hA t
            (X := ProjectiveLine S') (Y := ProjectiveLine S)
            (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
              (d S hS).invertible_on_projectiveLine).hom ≫ (d S' hS').trace) ∧
    ∀ K : DerivedCategoryModule A S,
      (ordinaryFinitePullback A f).map
          ((d S hS).adjunction.counit.app K) =
        ordinaryFiniteP1Exchange A f ((ordinaryFiniteP1Right A N hA S).obj K) ≫
          (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
            (ordinaryFiniteP1RightBaseChange A N hA t f
              (d S hS).invertible_on_projectiveLine K).hom ≫
          (d S' hS').adjunction.counit.app
            ((ordinaryFinitePullback A f).obj K)

end AlgebraicGeometry.Etale
