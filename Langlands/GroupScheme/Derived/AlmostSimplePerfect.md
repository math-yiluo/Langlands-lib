# Almost-simple perfectness and its generation consequence

This internal deduction uses the existing actual commutator-envelope
construction, the published definition of almost-simplicity, and full
derived-subgroup functoriality. It introduces no structural assumption in the
almost-simple case.

`IsAlmostSimple.derivedSubgroup_eq_top` proves, over every field and in every
characteristic, that the full scheme-theoretic derived subgroup functor of an
almost-simple actual group scheme is the total subgroup functor. Choose the
smooth geometrically connected closed commutator-envelope representative from
`smoothConnectedCommutatorImage`. Its range is the full derived subgroup and is
normal on every test scheme. Almost-simplicity makes that range trivial or
total. In the trivial case every test-scheme commutator is the identity, so
every pair of test points commutes, contradicting the noncommutativity clause.
The total case gives the required equality. Neither the base field nor its
characteristic is restricted.

`algebraicallyClosedSemisimplePerfect_of_almostSimpleGeneration` retains the
explicit premise `SemisimpleAlmostSimpleGenerationStatement`. Choose the same
closed derived representative for a semisimple group over an algebraically
closed field. Every normal almost-simple closed subgroup maps into this
representative: its own derived functor is total by the preceding theorem, and
full-derived functoriality carries every one of its test points into the
ambient derived functor. The generation premise therefore makes the chosen
representative's range total.

`semisimplePerfect_of_almostSimpleGeneration` composes this result with
`semisimplePerfect_of_algebraicallyClosed`. The latter extends a semisimple
group to an algebraic closure and descends equality with the total full
derived functor along the faithfully flat field extension.

These two semisimple consequences are conditional on the stated generation
proposition. This file does not prove that proposition and does not assert an
unconditional semisimple perfectness theorem. Its provenance is the internal
composition just described, rather than a new translation of a literature
statement.
