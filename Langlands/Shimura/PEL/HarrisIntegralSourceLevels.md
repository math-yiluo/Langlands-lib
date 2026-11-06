# Source-stabilizing refinements of actual Harris adelic levels

This internal construction proves that the integral source span used by the
original Harris Weil-frame normalization is open, that its actual two-sided
similitude stabilizer is open, and that every original compact-open level has
a compact-open sublevel contained in that stabilizer. It constructs the
sublevel and the original identity-element level-forgetting arrow. It does
not assume existence of a normalized frame, an integral abelian-scheme model
or a representing scheme.

## Data and provenance

The arithmetic carriers are universe zero. The inputs are the same number
fields `E` and `F`, their totally real and totally complex structures and
quadratic extension, the same algebra `A`, central simple unitary data `D`
and normalized Harris charts `C`. The rational scalar tower is retained.
The integer lattice is the constructed
`D.harrisHodgePELIntegralLattice C` from `HarrisIntegralPairing`, which makes
the unchanged Harris form integer-valued. This construction uses neither
a replacement form nor a supplied lattice.

Write `Af` for the actual `Global.FiniteAdeles ℚ`, `Rf` for its actual
`Global.integralFiniteAdeles ℚ` subring, and `Vf = Af ⊗[ℚ] A`.
The `Rf`-module structure is restriction along the subring inclusion. The
source span is exactly `D.harrisHodgePELIntegralAdeleSpan C`, generated over
`Rf` by `1 ⊗ x` for every element `x` of the constructed integer lattice.
The topology on `Vf` is `moduleTopology Af Vf`.

The group is the original
`ScalarExtensionSimilitudePoints A A Af (D.harrisHodgePELForm C)`.
Its operator topology observes the actual forward and inverse operators
pointwise and the unit multiplier. Its underlying group is the original
scalar-extension similitude subgroup. The subgroup used here is exactly
`harrisIntegralAdeleStabilizer D C`, whose defining condition is

`g(v) ∈ Λf ↔ v ∈ Λf` for every `v : Vf`.

The provenance is internal: this unit derives a finite-basis criterion from
the published lattice, finite-adele, topology and stabilizer constructions.
No external existence theorem or literature assertion is used. The generic
linear-algebra helpers are private and have the actual Harris consumer below.

## Openness of the actual span

The private `sourceIntegralBasis` is a finite integer basis of the actual
lattice. Its extension using `Module.Basis.extendOfIsLattice` is a rational
basis of `A` with the same vectors, viewed in `A`.

For a finite rational basis `b`, private `basisSpan` is the `Rf`-span of
`1 ⊗ b(i)`. The private membership lemma identifies this span with the vectors
whose coordinates in `b.baseChange Af` all belong to `Rf`. Span induction
proves the forward implication: generator coordinates are zero or one, and
addition and multiplication by integral coefficients preserve integrality.
For the reverse implication the finite basis expansion expresses a vector
as an `Rf`-linear combination of those same generators.

Every coordinate map is continuous for the canonical module topology.
`Global.isOpen_integralFiniteAdeles ℚ` and finite intersection therefore
prove that `basisSpan` is open. The private `sourceSpan_eq_basisSpan`
identifies the actual source span with the span for `sourceRationalBasis`.
One inclusion expands each integer lattice element in its integer basis;
additive-subgroup closure under integer multiples and finite sums suffices.
The other inclusion follows because each extended basis vector is the image
of an actual lattice element.

The public theorem `harrisHodgePELIntegralAdeleSpan_isOpen` consequently
proves openness of the actual source span, without a normalization premise.

## Openness of the actual stabilizer

A private span-induction lemma proves that an `Af`-linear map preserving the
finite generating vectors preserves the whole `Rf`-span. Thus membership
in the actual source stabilizer is equivalent to the conjunction of two
finite families of conditions: the forward operator sends every source
basis vector into the source span, and the inverse operator does so too.
The inverse family gives the reverse implication in the defining membership
equivalence by cancellation of the forward and inverse operators.

Each family defines a finite intersection of inverse images of the open
source span under continuous evaluation maps. Both evaluation continuities
are those of `ScalarExtensionSimilitudePoints`, so the proof uses the original
operator topology. The public `harrisIntegralAdeleStabilizer_isOpen` proves
openness of precisely this subgroup. `harrisIntegralAdeleOpenStabilizer`
equips the same subgroup with that proof; it changes neither its elements
nor its action.

## Compact-open refinement and original level arrow

Given any original
`K : FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)`,
`harrisIntegralSourceRefinement D C K` has open subgroup

`K.openSubgroup ⊓ harrisIntegralAdeleOpenStabilizer D C`.

The stabilizer, being an open subgroup of a topological group, is closed.
Intersecting this closed set with the compact set underlying `K` proves
compactness of the refinement. The needed rational finite-dimensionality
is derived locally from the finite rational source basis; it is not an
additional hypothesis. Thus the construction returns an actual level of
the original compact-open level type.

`harrisIntegralSourceRefinement_mem` states that membership in the refinement
is exactly membership in `K` and the original stabilizer.
`harrisIntegralSourceRefinement_le` proves containment in `K`, and
`harrisIntegralSourceRefinement_le_stabilizer` proves containment in the
original source stabilizer, with the underlying subgroup convention used
by `HarrisIntegralTateImages`.

`harrisIntegralSourceRefinementArrow` is the original
`CompactOpenLevel.inclusion` arrow from this refinement to `K`. Its transporter
is the identity, and its subgroup-respect condition is the proved containment.
No modified action, quotient or level category is introduced.

## Scope

Every existing compact-open level therefore has a concrete compact-open
sublevel for which the source-stabilizer premise in the original integral
Weil-level normalization results is satisfied. The subgroup itself is proved
open; compactness of the entire stabilizer is not asserted.

The construction does not prove normalized-frame existence on any abelian
scheme, denominator reflection of a rational isomorphism, existence of an
ordinary PEL moduli scheme or a natural comparison with the normalized CM
presheaf. It supplies no admissibility, smoothness or projectivity result.
The exact division CM representability target remains a separate obligation.
