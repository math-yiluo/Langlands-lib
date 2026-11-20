# Constituent recovery from Jacquet–Shalika trace independence

Lean module `Langlands.Automorphic.Unramified.CuspidalSpectralRigidityReduction`.
The proof is adapted from Worker 3657’s shared draft for Task 6446, revision 7.

`CuspidalSpectralRigidityReductionStatement.{uF, uV}` is the implication from the
published `CuspidalPowerTraceIndependenceStatement` to the published conjunction
`CuspidalSpectralRigidityStatement`. The theorem
`cuspidalSpectralRigidity_of_independence` proves that implication. The premise
supplies the trace independence of Jacquet–Shalika II, Theorem 4.2. The proof
derives the power-trace and Euler-polynomial recovery conjuncts with both
universes and all original hypotheses. The three auxiliary propositions ending
in `At` are the bodies of the published conjuncts over one fixed number field.
The fieldwise implications allow the argument to apply also over totally
complex fields when trace independence is supplied there.

## Recovering the constituents from power traces

First, two spectra attached to the same full cuspidal class give the same power
traces off their two exceptional sets. The first attachment supplies a
realization and presentation. The proof moves the other attachment to a second
presentation of that realization with `IsoClass.hasSpectralSystem_iff`, then
applies the Library's `CuspidalSpectralPresentation.spectralSystem_eigenvalues_eq`.

Combine the two index types `Fin p` and `Fin q` into their sum. Choose a
representative index of each class in the combined family and enumerate those
representatives by a `Fin` type. The representative family is injective. Every
original index contributes `1` or `−1` according to its list, so the sum of these
signs over a representative's fibre is the difference of its two multiplicities.
The empty combined family gives the equivalence of the two empty index types
directly.

At a place outside all the exceptional sets and the finite set excluded by the
trace comparison, `SpectralSystem.finiteSum_samePowerTraces_iff` gives equality
of the two sums at every positive power. Replace each trace by its
representative's trace and group the signed sum by representatives using
`Finset.sum_fiberwise_of_maps_to`. Trace independence makes every resulting
coefficient zero. The equality of the two fibre cardinalities yields an
equivalence of the fibres over every representative by `Fintype.equivOfCardEq`.
Composing these equivalences with the two fibre decompositions gives the
required index bijection, preserving the full cuspidal class.

## Recovering the constituents from Euler polynomials

At each tested place the roots of the denominator polynomial are the inverses
of the nonzero eigenvalues, with multiplicity, by
`Eigenvalues.eulerPolynomial_roots`. Equality of polynomials gives equality of
these root multisets. Injectivity of inversion and of the inclusion of complex
units into `ℂ` gives equality of the underlying eigenvalue multisets, allowing
for potentially different ranks in the input. This gives equality of their
positive power traces over the same cofinite set. The trace recovery theorem
then applies to the original finite sums.

## Source

H. Jacquet and J. A. Shalika, *On Euler Products and the Classification of
Automorphic Forms II*, American Journal of Mathematics **103** (1981),
777–815. Theorem 4.2, printed pp. 806–807 (one-based PDF pp. 31–32), supplies
trace independence. The proof of Theorem 4.4, printed p. 809 (PDF p. 34),
passes from the trace sums in (2) to the multiplicity comparison in (3)–(4).
The Lean argument starts at (2) and applies Theorem 4.2 to the union of the two
sets of classes. Comparison of independently attached presentations and the
Euler-polynomial implication are adaptations to the Library’s definitions.
Registered source `jacquet-shalika-1981-euler-ii`, SHA-256
`4d3f68841a558631a1624482d497665c2b52059bb9e0b7333948b8d1610b57d8`.
