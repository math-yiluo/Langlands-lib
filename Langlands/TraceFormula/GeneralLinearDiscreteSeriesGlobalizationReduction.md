# Ordinary globalization of a square-integrable representation from local selection tests

`GeneralLinearDiscreteSeriesGlobalizationReductionStatement` is the implication

`GeneralLinearDiscreteSeriesSelectionTestStatement.{u, uV, u}` →
`GeneralLinearSupercuspidalSelectionTestStatement.{u, u}` →
`GeneralLinearDiscreteSeriesGlobalizationStatement.{u, uV, uQ}`,

and `generalLinearDiscreteSeriesGlobalizationReduction` proves it. The hypotheses are the
two local propositions in `GeneralLinearLocalSelectionTestStatement`. The global argument
uses the Hilbert–Schmidt property of cuspidal tensor operators from
`GeneralLinearTensorCuspidalHilbertSchmidtPositiveRank`.

This is the trace-formula argument of Arthur–Clozel (1989), Chapter 1, Lemmas 2.4 and 6.5
(printed pp. 13–14 and 54–55), with orbit isolation as in Henniart–Lemaire (2011),
II.6.7–II.6.9 (printed pp. 123–125). The local tests select up to unramified twists on the
full space of the positive rational quotient, where the proof uses the Library's ordinary
simple trace formula.

1. The global data are the split central torus of scalar matrices
   (`GroupScheme.GeneralLinear.scalarTorus`), `parabolicDynamic` and
   `normOneHaarRightInvariant`.
2. The square-integrable selection test at `v₀` for `ρ` and the supercuspidal selection tests at
   `v₁` and `v₂` give local tests with nonvanishing orbital integrals on nonempty open sets; the
   test at `v₁` has vanishing constant terms.
3. `exists_globalTest_trace_ne_zero` gives a global tensor test with these local factors whose
   operator is trace class, maps into the cuspidal subspace and has nonzero trace.
4. `exists_irreducibleSummand_compressedTrace_ne_zero`, with
   `generalLinearFullAEL2CuspidalCompactness`, gives an irreducible closed invariant cuspidal
   subspace `P` on which the compressed trace is nonzero.
   `generalLinearCuspidalSummandRealization` realizes `P` by a cuspidal operator realization
   `R`. The results `cuspidalIrreducibleAdmissibleFiniteSliceExistence`,
   `CuspidalOperatorRealization.exists_presentation_of_finiteSlice` and
   `CuspidalSpectralPresentation.exists_small` give a spectral presentation `D` of `R`, in the
   universe `uQ`, with irreducible admissible components.
5. `hasUnitaryCentralCharacter_of_formClass` gives the unitary central character. At each of
   `v₀, v₁, v₂` the test is rewritten as the local factor times a function invariant at that
   place, and `exists_distribution_ne_zero_of_compressedTrace` shows that the character of the
   local component of `D` does not vanish at the local test.
6. The local component at `v₀` is unitarizable (`cuspidalUnitaryLocalUnitarity`) and generic
   (`CuspidalSpectralPresentation.exists_generic_at_completion`), so the square-integrable
   selection test identifies it with a unitary unramified determinant twist of `ρ`. The
   supercuspidal selection tests make the components at `v₁` and `v₂` supercuspidal, and
   `localRealization_isSupercuspidal_of_matrixAction` converts this to
   `LocalRealization.IsSupercuspidal`.
