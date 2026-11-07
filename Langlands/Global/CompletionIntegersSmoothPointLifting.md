# Smooth point lifts over actual completion integer rings

This derived construction supplies the Henselian completion-ring step in
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), Theorem 4.5, printed p.12, third proof paragraph. It uses the actual
height-one adic completions and the actual completions at discrete curve
places. The coefficient ring is arbitrary, and neither scheme is assumed
affine.

The generic Henselian helper first imports the published theorem
`Langlands.NYLL.ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdicComplete`.
For a field complete for its supplied rank-one discrete valued uniformity,
that theorem gives maximal-ideal adic completeness of its native valuation
subring. Mathlib's `IsAdicComplete.henselianRing` then gives Henselianity at
that maximal ideal. A unit derivative remains a unit under the quotient
map, so `HenselianRing.is_henselian` supplies exactly the condition required
by `HenselianLocalRing`. The field and value group have independent
universe levels.

`adicCompletionIntegers_henselian` specializes this result to an arbitrary
height-one prime of a Dedekind domain and its fraction field. Mathlib
supplies completeness and discreteness for this native completion.
The original domain and fraction field have independent universes.
`curvePlaceCompletionIntegers_henselian` applies the same result to the
height-one prime of the original valuation ring of an actual curve place.
Neither specialization assumes residue finiteness, a number field, a
finite constant field, or a chosen parameter for the function field.

`adicCompletionSmoothPointLift` takes an actual relative morphism
`f : X ⟶ Y` over `Spec C` with smooth underlying morphism, an integral
point `p` of `Y`, and a point `q` of `X` over the actual residue field of
the completed integer ring. Its compatibility premise says exactly that
`q` maps to the reduction of `p` under the canonical residue map. The
constructor returns an actual integral point `a` of `X`, together with
both equalities: `a ≫ f = p` and the reduction of `a` equals the originally
supplied `q`. It installs the proved Henselian instance locally and applies
the published `henselianSmoothPointLift` to the surjective residue map.
`curvePlaceCompletionSmoothPointLift` is the specialization to the actual
curve-place completion. All relative points are the existing
`RingPoint C X R` morphisms in `Over (Spec C)`.

These are noncomputable choices of actual integral lifts. Their native
rings and topologies are unchanged. This unit does not construct residue
points or prove residue-cardinality growth, a Lang–Weil estimate,
spreading, or adelic openness. Those remain separate parts of the parent
task.
