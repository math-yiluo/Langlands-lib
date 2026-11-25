/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalBaseChange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalTriangles

/-!
# The diagonal unit for the Kummer-normalized projective-line trace

Source: blueprint proposition-adjunction-projective-line--1 and
lemma-class-diagonal-projective-line. (auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [local irreducible] ordinaryFinitePullback ordinaryFinitePushforward
  ordinaryFiniteTensor

-- Preserve the existing binder names in the public statement.
set_option linter.unusedVariables false in
/-- The supported diagonal gives a unit for the already specified trace counit.
The decomposition and Chern arrows are inputs; no decomposition is asserted here.
Source: blueprint thm-amb-p1-adjunction.md and its proof;
lem-amb-p1-diagonal-integrals.md and its proof.
(auxiliary; not a blueprint node).

Proof: Apply the supported Cartier Kummer construction to the diagonal of P times_S P.
Its existing component formula, in either projective-line chart, expresses the pushed
class as a base Chern component followed by the twisted unit plus the relative Chern
pushforward. The second projection of the Kummer-normalized splitting kills the
first component and evaluates the second to one. This gives both scalar diagonal
integrals with the specified source units and coefficient comparisons.
For every complex M, invert the diagonal projection formula, tensor with the supported
class, push along the second projection, and apply inverse proper exchange and the
ordered projection comparison. These natural maps define the common-base unit.
The two coordinate trace contractions identify its triangular composites with the
tensor section integrals. Naturality interchanges the coordinates in the first
triangle; restriction of the coordinate comparison to the diagonal handles the
second. The scalar integrals and the section projection identities make both
composites identity. The normalized shifted-line pullback identifies the common-base
coefficient with the prescribed projective-line right adjoint. Projection naturality
identifies the transported counit with the specified Kummer trace counit.
For base change, invert the decomposition square and apply its second projection to
obtain the scalar trace square. The canonical projection/exchange mate square tensors
this scalar equation with an arbitrary complex. Insert the inverse ordered projections
and the normalized constant-unit square; their composite is exactly the stated counit
base-change equation. All arguments apply to unbounded complexes without an added
flatness or boundedness hypothesis. -/
theorem ordinaryFiniteP1_diagonal_unit (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (c : OrdinaryFiniteP1ChernFamily A N hA)
    (hc : OrdinaryFiniteP1ChernFamilySpec A N hA c)
    (b : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
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
              ((ordinaryFiniteP1TraceCounit A N hA S (b S hS)).app K) = 𝟙 _)) ∧
    (∀ {S' S : Scheme.{u}} [IsNoetherian S'] [IsNoetherian S]
      (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤)))
      (K : DerivedCategoryModule A S),
      (ordinaryFinitePullback A f).map
          ((ordinaryFiniteP1TraceCounit A N hA S (b S hS)).app K) =
        ordinaryFiniteP1Exchange A f ((ordinaryFiniteP1Right A N hA S).obj K) ≫
          (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
            (ordinaryFiniteP1RightBaseChange A N hA t f
              (affineTraceProjectiveInvertible N S hS) K).hom ≫
          (ordinaryFiniteP1TraceCounit A N hA S' (b S' hS')).app
            ((ordinaryFinitePullback A f).obj K)) := by
  exact ⟨ordinaryFiniteP1_diagonal_triangles N hN A hA t c hc b hb hbc,
    ordinaryFiniteP1_diagonal_baseChange N hN A hA t c hc b hb hbc⟩

end AlgebraicGeometry.Etale
