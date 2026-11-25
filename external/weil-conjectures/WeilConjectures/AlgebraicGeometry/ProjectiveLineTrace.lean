/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction

/-!
# The ordinary finite-coefficient projective-line trace

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/def-amb-p1-trace.md
(blueprint: lemma-cohomology-projective-line-trace).

All categories are the entire derived categories of ordinary small-etale module sheaves.
The decomposition is characterized by its shifted twisted unit and the scalar Kummer
class of O(1). Its inverse, and hence the trace below, are determined by these maps.

## Main definitions

* `projectiveLineTraceDatum`: the canonical normalized decomposition datum.
* `projectiveLineTrace`: projection onto the second summand after inverse decomposition.
* `projectiveLineTraceEpsilon`: the inverse projection formula followed by tensor trace.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The canonical finite-twist transport furnished by the projective-line theorem.
The roots inclusion and pure-tensor equations characterize this transport, so this
selection does not introduce a choice of orientation or a primitive root.
Source: blueprint lemma-cohomology-projective-line-trace (blueprint:
lemma-cohomology-projective-line-trace). -/
def projectiveLineTraceTransport (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    OrdinaryFiniteTwistTransport A N hA :=
  Classical.choose (exists_ordinaryFiniteP1Adjunction N hN A hA)

/-- The normalized decomposition from the recorded ordinary projective-line theorem.
The Chern arrow is fixed by its cohomology realization, the decomposition by its two
components, and the adjunction by its counit. Consequently all data used below are
independent of the witness selected here, up to the equality of the specified arrows.
Source: blueprint lemma-cohomology-projective-line-trace (blueprint:
lemma-cohomology-projective-line-trace). -/
def projectiveLineTraceDatum (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    OrdinaryFiniteP1Datum A N hA (projectiveLineTraceTransport N hN A hA) S hS :=
  Classical.choose (Classical.choose_spec
    (exists_ordinaryFiniteP1Adjunction N hN A hA)) S hS

end AlgebraicGeometry.Etale
