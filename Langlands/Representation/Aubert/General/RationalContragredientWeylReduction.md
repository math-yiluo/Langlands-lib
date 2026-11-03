# Rational duality reduction using actual longest lifts

This internal construction specializes the generic conjugate-Jacquet and
Weyl-class duality reduction to the actual rational standard and opposite
families. Every additional closed structural or representation proposition
remains an explicit input. The module does not prove the closed rational
contragredient commutation target or any of those input propositions.

`associatedOppositeJacquetFiniteLengthObject` has as underlying representation
the actual normalized opposite Jacquet object of the given finite-length
ambient object. Its opposite cocharacter is selected by
`standardCocharacterForDuality`, retaining its standard-root-subset witness.
The construction chooses `longestSchemeNormalizerLift` and uses its actual
inverse point-normalizer element. The three membership equivalences of
`associatedOpposite_mem_of_structural` identify the opposite groups with the
standard groups at `associatedSubset cs I`. Applying
`conjugateJacquetFiniteLengthObject` to the Levi and radical equivalences
transfers standard Jacquet finite length to the literal opposite object.
This construction needs the displayed Coxeter realization and structural
transport, but no natural-duality or admissibility input.

`standardContragredientTermComparison_of_schemeWeylDuality` applies
`contragredientTermComparison_of_duality_of_weylConjugacy` to the same actual
families. Its reindexing is `associatedSubsetEquiv cs`; the proved cardinality
law preserves the original alternating coefficients. Its normalizer family
is the inverse of the chosen scheme longest lifts. The three subgroup
comparisons are exactly the membership equivalences just described. The
standard induced-class premise is obtained by specializing the explicit
closed `RationalInducedClassWeylConjugacyStatement` input. The actual Jacquet
and induction duality isomorphisms are supplied by
`finiteLengthJacquetDualityIso` and `finiteLengthInductionDualityIso`, using
these four explicit closed inputs:

- `RationalNaturalJacquetDualityStatement`;
- `RationalNaturalInductionDualityStatement`;
- `RationalPointsFiniteLengthAdmissibleStatement`;
- `DynamicLeviFiniteLengthAdmissibleStatement`.

The generic reduction derives opposite Jacquet finite length by actual
conjugation and obtains the opposite/standard induction-class equality from
the supplied standard induced-Weyl class identity. Neither must be added as
a separate hypothesis. The output is exactly the original
`standardContragredientTermComparison`, with its original standard-family
finite-length, topological and ambient-dual premises. Ambient compact-open
cofinality is derived from the nonarchimedean group topology.

`rationalContragredientCommutation_of_schemeWeylDuality` makes the remaining
closed proof boundary explicit. From the additionally supplied
`RelativeWeylCoxeterStatement` it obtains finiteness of the actual simple-root
labels and scheme relative Weyl group and chooses the stated Coxeter system.
It specializes the additionally supplied
`StandardAssociatedOppositeTransportStatement` and
`StandardLeviConjugationStatement` and applies the term comparison above.
Finally it uses `rationalContragredientCommutation_of_termComparison` to
conclude the unchanged `RationalContragredientCommutationStatement`.
This is a conditional implication with eight extra closed proposition inputs,
not an unapplied proof of that target. Their separately owned proofs and
publication remain required; none is converted into an external structural
assumption by this module.

The scope remains every connected reductive group scheme over every
nonarchimedean local field, including positive characteristic and nonsplit
and non-quasisplit groups, with the canonical evaluation `pointTopology`.
The independent universes are `u` and `v`, and representation carriers have
universe `max (u + 1) v`. Root labels are literally `SimpleRoot i ν`, including
the empty type. All groups, normalized functors and the exact finite-length
Grothendieck group with its actual short-exact-sequence relations are the
published ones. No point/scheme normalizer equality, centralizer comparison
or quotient equivalence is used.

The provenance is composition of the named internal constructions. Worker
490 authored the generic Weyl reduction; Worker 1107 authored the outer
transport predicate and point-evaluation adapter. No new literature assertion
is made. The implemented proof bodies use no Langlands classification,
character independence, geometric lemma, adjointness or cuspidal-support
theorem. The finite-length reflection in the generic Jacquet helper uses the
surjective invariant-subspace order equivalence described in that helper's
Markdown, independently of the surrounding classification and cuspidal-support
modules' other results. Dependencies of future proofs of the eight explicit
closed inputs remain separate and must be audited when consumed.
