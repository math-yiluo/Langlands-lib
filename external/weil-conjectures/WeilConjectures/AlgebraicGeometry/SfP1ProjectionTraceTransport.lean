/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1ChartExchange
import WeilConjectures.AlgebraicGeometry.SfP1ProjectionTraceTransportFalse
import WeilConjectures.AlgebraicGeometry.SfP1ProjectionTraceTransportTrue

/-! # Transport of an ordinary exchange trace across a projective-line isomorphism

This comparison is natural in an arbitrary arrow out of the direct-image object.
It does not refer to a chart trace or a family of projective-line splittings.
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- Inverse exchange transports an arbitrary ordinary trace through an isomorphism
of projective lines. This uses no base-change property of that trace.

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, the paragraphs using qp1 = qp2 and the
composite-adjunction counit (auxiliary; not a blueprint node).

Proof: Substitute projectionExchange, middleComparison and coordinateTrace.
Use naturality of proper forget-supports to replace compact-support exchange by
ordinary exchange. Paste the self-product square for i with the product square
for q. The mate pasting law identifies the resulting exchanges with the one for
f = i followed by q. In the direct-image composition comparison, substitute the
composite-adjunction counit. The inverse-image/direct-image factors for i cancel
through pushPull, giving exactly the prefix of the explicitly defined trace.
Naturality moves the arbitrary arrow tau through the remaining exchange factors.
For the twist comparisons use their roots and pure-generator normalizations:
monicity of the root inclusion and generation by pure scalars imply compatibility
with composition and with each of the two product squares. In the second square
both composites to S agree, so the inverse coordinate comparison is exactly the
additional factor in coordinateTrace at true. The constant sheaf unit is preserved
by inverse image; after the single-degree and derived tensor-unit comparisons its
unit equation identifies the final constantComparison with pullback of constantUnit
followed by leftDerivedUpperStarDerivedTensorUnitIso. These identities give the
stated equation. All manipulations are natural in tau, and neither a splitting,
a trace base-change equation nor a diagonal integral is used. The same calculation
works for the empty base and zero coefficient ring. -/
theorem projectionTraceTransport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (N : Γ(S, ⊤)))
    (τ : ordinaryFiniteP1SplittingTarget A N hA S ⟶ ordinaryFiniteUnit A S)
    (a : Bool) :
    middleComparison A N hA t f i hi hS a ≫
        (ordinaryFinitePullback A i.hom).map (projectionExchange A N hA t S hS a) ≫
        (ordinaryFinitePullback A i.hom).map
          ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).map τ ≫
            (ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom) ≫
        (constantComparison A i).hom =
      coordinateTrace A N hA t f i hi hS τ a := by
  cases a
  · exact projectionTraceTransport_false A N hA t f i hi hS τ
  · exact projectionTraceTransport_true A N hA t f i hi hS τ

end AlgebraicGeometry.Etale.SfP1Transport
