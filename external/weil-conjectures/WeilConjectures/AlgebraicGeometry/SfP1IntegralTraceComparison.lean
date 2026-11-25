/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals
public import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData
import WeilConjectures.AlgebraicGeometry.SfP1ProjectionTraceTransport

/-! # Transport of the two projection traces

This equation concerns a fixed explicit trace and needs no diagonal Ext class.
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- The base-change equation for the splitting trace identifies the two chart
traces with the coordinate traces of the explicitly transported trace.

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, the paragraphs identifying t_p1 and t_p2 with
base change of t_q and the equality qp1 = qp2.
(auxiliary; not a blueprint node).

Proof: Apply the trace clause of hbc to the projective-line structure morphism
P -> S. The canonical projective-space base-change isomorphism is the chart
used by ordinaryFiniteP1DiagonalChartMap for the second projection, and the
flipped square gives the first projection. Substitute the definition of that
chart map and the exchange mate. Its pullback counit, composed with the chart
unit, cancels by the adjunction triangle. This identifies each chart trace
with inverse ordinary exchange followed by pullback of (d S hS).trace.
Paste with i and its self-product. Substitution of the composite-adjunction
counit gives pushPull and the composition comparison in the explicit trace.
Naturality of proper forget-supports identifies ordinary exchange with the
compact-support exchange used by coordinateTrace. Normalize all twist maps on
roots and pure scalar generators: uniqueness of those maps gives their
composition and square equations. For the second projection use p1 f = p2 f;
this is exactly the coordinate correction in coordinateTrace. The constant
unit comparison commutes with these inverse images and cancels the source and
target constant comparisons. These substitutions give the displayed equation
for both Boolean choices. No diagonal class or integral identity is used, and
the computation also applies to the empty base and to zero coefficients. -/
theorem traceComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t T hT)
    (hbc : ArbitraryBaseFiniteP1BaseChange A N hA t d)
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    middleComparison A N hA t f i hi hS a ≫
        (ordinaryFinitePullback A i.hom).map
          (arbitraryBaseFiniteP1DiagonalTrace A N hA t d S hS a) ≫
        (constantComparison A i).hom =
      coordinateTrace A N hA t f i hi hS (d S hS).trace a := by
  have htrace := (hbc (ProjectiveLine S ↘ S) hS
    (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS)).2
  have hchart : arbitraryBaseFiniteP1DiagonalTrace A N hA t d S hS a =
      projectionExchange A N hA t S hS a ≫
        ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).map (d S hS).trace ≫
          (ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom) := by
    rw [arbitraryBaseFiniteP1DiagonalTrace, ← chartExchange A N hA t S hS a]
    simpa only [Category.assoc] using
      congrArg (fun z ↦ projectionExchange A N hA t S hS a ≫ z) htrace.symm
  rw [hchart, Functor.map_comp]
  simpa only [Category.assoc] using
    projectionTraceTransport A N hA t f i hi hS (d S hS).trace a

end AlgebraicGeometry.Etale.SfP1Transport
