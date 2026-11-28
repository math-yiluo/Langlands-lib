# The ambient round trip at the translated parabolic

`exists_weightedC_ambientRoundTrip` starts from the ambient density package
`PG` for the original standard parabolic and assumes
`hPG : PG.canonicalScalar ≠ 0`. The package scalar is written as a quotient
`a/b` of regular functions (`package_compact_spec`), and `hPG` makes `a`
nonzero. Its
conjugation by `n` and change of compact subgroup
(`exists_conjugatedChangedCompact_canonicalScalar`) identify it with the
round trip of the opposite pair at the translated vertex `θ`, up to one
positive Haar factor `t₀`. `oppositeForwardContinuedPair_eq` and
`oppositeReverseContinuedPair_eq` compare the two operators of that round
trip with the continued compact operators of the given system `p`. The
fractions are moved to the translated parameter scheme by
`rationalUnramifiedRegularFunctionsEquiv` and compared through
`rationalFunction_value_eq`.

The lemma provides nonzero regular functions `Gnum`, `Gden` and `c₀`. On
the regular region of the opposite pair at `θ` where `c₀` does not vanish,
the round trip equals `t₀ · Gnum/Gden` times the identity. On the weighted
domain, wherever `Gnum` does not vanish, the ambient density value is the
density constant times `Gden/Gnum`
(`packageDensity_value_of_scalarFraction`, `weightedC_restrict_ambientDensity`).

The scalar is `j(ω)` of Waldspurger IV.3, printed p. 285. Its invariance
under conjugation is IV.3(3), printed p. 286, and the density
`µ = j⁻¹ ∏ γ(M_α|M)²` is defined in V.2, printed p. 292 (source `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). The Haar
factor compares the measures for the transported compact
`n PG.K n⁻¹` with those for `K`. Each quotient measure uses Haar measures
normalized to give mass one to the intersections with its own compact
subgroup, as in I.1, printed pp. 240–241.
