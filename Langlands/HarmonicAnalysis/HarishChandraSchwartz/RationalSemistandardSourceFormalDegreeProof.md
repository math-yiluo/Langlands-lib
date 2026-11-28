# Formal-degree transport to the actual semistandard Levi model

`Langlands.HarishChandraSchwartz.RationalSemistandard.SourceDegree.formalDegreeTransport`
proves the Library's `FormalDegreeTransportStatement`. For each discrete-series
class of the literal semistandard Levi, its formal degree for the displayed
quotient Haar is the degree of `SourceMeasure.intrinsicDiscreteSeriesClass`
for `SourceMeasure.intrinsicQuotientHaar` on the scheme-point Levi. The group
identification is `LeviModel.pointHomeomorph`, and the quotients use the actual
split-center images. The theorem retains arbitrary nonarchimedean local fields
and independent field and representation-carrier universes. As in the target,
there is no separate affineness hypothesis on the source of the split component.

This is an internal transport of the Schur normalization in [Waldspurger
(2003)](https://doi.org/10.1017/S1474748003000082), III.1 (3), printed p. 265
(PDF p. 31), registered as `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The comparison uses the prescribed pullback measure; it does not compare
independently normalized Haar measures.

## Lean proof

The private helper `Langlands.Plancherel.representationFormalDegree_pullback` uses the same
algebraic functionals on both representations: smoothness is transported by
`isSmoothVector_dual_comp_continuousMulEquiv_iff`. On a quotient representative
`x` of the model group, the two Schur integrands agree at `x` and its image
because the equivalence preserves inversion. The quotient pushforward
identity and `integral_map_equiv` give equal orthogonality integrals. The
Schur formula on the model group therefore supplies the normalization on
the literal group too, and `formalDegree_unique` identifies the degrees.

For the actual Levi groups, the proof uses quotient induction to take an
irreducible admissible representative of the input class.
`isSquareIntegrableModCentralSubgroup_comp_iff` gives square integrability of
its pullback using `SourceMeasure.map_intrinsicQuotientHaar`. The proof
then applies the helper to these representations and uses
`discreteSeriesFormalDegree_mk` on both sides to obtain equality for the
prescribed classes.
