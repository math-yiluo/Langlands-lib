# Spectrum detection of ideals and units

The theorem `spectrumIdealCriterion` proves the published `SpectrumIdealCriterionStatement K` for every
complete ultrametric normed field, including trivial valuations and the zero
quotient. The three conjuncts are proved without adding any hypotheses. They
are the helper theorems `exists_spectrum_kernel_of_proper_ideal`,
`isUnit_iff_forall_spectrum_ne_zero` and
`span_range_eq_top_iff_forall_spectrum_exists_ne_zero`, all in
`Langlands.Analytic.PresentedStrictAffinoidAlgebra`.

For a proper ideal over trivially valued scalars, that is when every scalar has
norm at most one, the helper
`exists_spectrum_kernel_of_proper_ideal_of_scalar_norm_le_one` chooses an actual
maximal ideal containing it and uses the previously constructed point
`primePoint_of_scalar_norm_le_one`, obtained by pulling back the trivial
multiplicative seminorm of that maximal quotient. Membership in the maximal
ideal makes the quotient class zero. This helper does not require completeness
of the scalar field.

Otherwise some scalar has norm greater than one, and the proof uses it to
regard `K` as a nontrivially normed field. Pull the ideal back along the actual
finite Tate presentation. The preimage is proper because the presentation
preserves one. The published closed-ideal theorem for Noetherian Banach
algebras, `isClosed_ideal_of_noetherian_banach`, shows that this preimage is
closed. Its quotient therefore defines another actual presented strict affinoid
algebra, which is nonzero because the ideal is proper. Spectrum nonemptiness,
`spectrum_nonempty`, supplies a point of that quotient. Pull it back to the
Tate algebra; it annihilates the original presentation ideal. The existing
bounded-seminorm descent construction `BanachSpectrum.descend` gives a point of
the original affinoid. Surjectivity of the presentation shows that it
annihilates the given ideal. There is no closedness hypothesis on that ideal
and no assumed point.

The two algebraic consequences use that every spectrum point has a proper prime
kernel. If a singleton or finite family generates the unit ideal, it cannot lie
in such a kernel. Conversely, a proper generated ideal admits an annihilating
point by the preceding construction. The finite-family argument also applies
to the empty family; it does not introduce a nonzero-algebra assumption.

The source provenance of the unchanged target is the canonical inclusion of
maximal ideals into the spectrum just before Proposition 2.5.6 on page 9 of the
retained fourteen-page notes of Berkovich's *Affinoid algebras* course
(`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`).
The implemented proof instead derives the realization from the nonemptiness
result and the closed-ideal theorem, whose source is Proposition 2.3.4 on page 6.
The unit and finite-family criteria are elementary consequences of realization.

Worker 56 authored this proof and explanation. Worker 224 added the
declaration names and the nontrivially-normed-field remark to this explanation.
