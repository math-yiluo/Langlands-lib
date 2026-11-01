# Scalar rational descent over the whole spectrum

Author: Worker 146.

`Langlands.Analytic.StrictTestDomain.wholeSpectrumRationalGluing.{u}`
proves the unchanged published
`WholeSpectrumRationalGluingStatement.{u}`. It gives a unique base element
for every compatible family of scalar sections of the actual unit-radius
rational quotient algebras in a finite cover of the whole base spectrum.
Compatibility is equality after the actual restrictions to every
ordered-pair intersection quotient. The coefficient field is any complete
ultrametric normed field, and the base is a presented strict affinoid
algebra. The theorem is unapplied and polymorphic in the same arbitrary
universe `u` as the published target.

The final theorem applies
`wholeSpectrumRationalGluing_of_nontrivial_standard` to the published
`nontrivialStandardRationalGluing` theorem. The conditional assembly helper
already uses the published `finiteRationalRefinement` and
`trivialScalarRationalLocalization` proofs. Thus the final theorem has no
additional localization, standard-cover descent, exactness, separation or
sheaf hypothesis. The target pair and its imports are unchanged.

The implemented assembly in `WholeSpectrumConditionalAssembly` first treats
an empty covering index. The point-cover hypothesis makes the base spectrum
empty. The preparation module uses spectrum nonemptiness for every nonzero
presented strict base to show that the base is zero, and its empty-cover
lemma supplies the unique lift of the empty tuple of sections.

For a nonempty covering index, the proof splits on whether a scalar has norm
greater than one. In that case, `finiteRationalRefinement` supplies a standard
rational cover refining the given finite cover. For each standard member,
choose a containing original rational locus. Its actual inclusion gives the
restriction map for pulling the original section to the refinement.
`WholeSpectrumRefinementAdapter` applies `ScalarCoverDescent.of_refinement`
using the proved standard-cover descent.

Recovering every original section also needs separation on the pullback
refinement over that original quotient. The actual pullbacks of a standard
cover are definitionally the standard cover for the mapped tuple.
`tuple_no_common_zero_pullback` supplies its no-common-zero condition.
Applying the standard-cover theorem to this quotient base and then
`ScalarCoverDescent.separated` provides the needed local separation.
The transfer therefore proves both existence and uniqueness for the
original family, with its actual base maps and restrictions.

If no scalar has norm greater than one, every scalar has norm at most one.
The published `trivialScalarRationalLocalization` theorem makes every actual
rational quotient an ordinary localization at its denominator.
`WholeSpectrumLocalizationAdapter` uses the point cover to prove that these
denominators generate the unit ideal, identifies the actual overlap maps
with the canonical localization maps, and applies Mathlib's
`Localization.existsUnique_algebraMap_eq_of_span_eq_top`. Selecting one
member per denominator is supplemented by a map back from the intersection
with every other member having that denominator. Compatibility and this
left inverse recover every original section, including repeated
denominators. The adapter's Markdown describes that algebraic argument.

The mathematical provenance is the scalar degree-zero, unit-radius
specialization of Berkovich, *Non-archimedean analytic spaces*, Trieste
lectures (2009), Fact 2.2.6(i), printed/PDF p.10, with the actual rational
quotient and intersection setting of Exercise 2.2.2(ii)-(iii), p.9.
The retained source is registered as
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
These passages were read directly; no source-specific registered errata
were present when read. They provide provenance rather than a formal
acyclicity assumption. The implemented proof instead uses the separate
proved standard-cover induction, geometric refinement and trivial-scalar
localization, followed by the explicit formal and algebraic adapters above.
The source and proof routes of those imported results are documented in
their paired Markdown.

Worker 146 authored the localization adapter, the standard-refinement
specialization and the final assembly. Worker 101 contributed the shared
preparation and standard-cover interface, and Worker 572 contributed the
shared formal descent transport. Their published modules are imported by
Lean name, as are the separately proved analytic prerequisites.

Empty covering types, empty numerator tuples and rational loci, zero and
nonreduced bases, and trivial scalar valuations remain in scope. No
nonzero-base, reducedness, nonempty-locus or nontrivial-valuation restriction
is inserted. The conclusion is scalar degree-zero descent at unit radii
over presented strict bases. It does not assert higher Cech exactness,
admissibility, finite-module descent, arbitrary radii, representation on
all affinoid tests, relative rational-target gluing or a categorical sheaf
theorem. The relative parent task and categorical conversion remain
separate obligations.
