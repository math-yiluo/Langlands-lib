# Compact compression over a Noetherian coefficient ring

Worker 1755, with reuse guidance from Worker 1751. An internal
coefficient-linear adapter for the argument in
Renard 2026 VI.9.2, printed p.199 / PDF p.205, using the actual localization
comparison from VI.9.1 and the final proposition in Appendix C.II,
printed p.279 / PDF p.285. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The two actual complex fixed-vector carriers are given module structures over
a commutative coefficient ring `R`. The actual compressed action, actual fixed
Jacquet quotient, and actual central Levi action must each respect the given
coefficient scalars. The internal `CompressionCoefficients.map` and `.equiv`
retain these actual functions as coefficient-linear maps and equivalences.
The construction changes none of their values.

The geometric setting is exactly that of `CompressionLocalization`: an
arbitrary topological group, compact open `K`, actual subgroups
`N`, `M`, `Nbar`, `M ≤ normalizer N`, the published
`IsIwahoriContraction K N M Nbar g`, and
`∀ m ∈ M, m * g = g * m`. The representation is a smooth complex
representation. The two additional `Module R` instances use the existing
additive groups on the actual complex fixed-vector carriers. Their
compatibility conditions `hC`, `hj`, and `hβ` are the pointwise scalar laws
for compact compression, the restricted quotient, and
`fixedJacquetCentralEquiv`, respectively.

No algebra map between `ℂ` and `R` or relation between their scalar actions
is needed by this internal adapter: the three displayed scalar laws supply
exactly the compatibility its proof uses. A universal-family application
still has to construct its intended coefficient actions and prove these
laws; arbitrary coefficient actions are not asserted to exist.
`CompressionCoefficients.map_pow_apply` and `.equiv_pow_apply` prove that
every forward power retains the original function, including exponent zero.
The inverse of `.equiv` is coefficient-linear by bijectivity of its forward
coefficient-linear map.

The previously constructed geometric kernel and exhaustion lemmas apply to
the retained maps, so the actual coefficient-ring localization of compression
is coefficient-linearly equivalent to the actual Jacquet fixed-vector module.
The equivalence sends the canonical localization arrow to the actual quotient
and intertwines the localized endomorphism with the actual unnormalized
central Levi action.
The constructed equivalence is
`Jacquet.coefficientCompressionJacquetLocalizationEquiv`.
Its `_iota` and `_intertwines` theorems are the two compatibility laws.
This construction does not require Noetherianity or finite generation.
The coefficient, group and representation-carrier universes are independent;
the coefficient localization has universe the maximum of coefficient and
representation-carrier universes.

When `R` is Noetherian and both actual fixed-vector carriers are finitely
generated over `R`, the inverse equivalence makes the actual localization
finitely generated. The published `finiteActualLocalizationStatement` gives
surjectivity of its canonical arrow and a positive stable compression power.
The canonical-arrow equation gives surjectivity of the actual Jacquet
fixed-vector quotient. The pointwise power laws for the retained maps transfer
both kernel and range stability equalities back to the original complex
compressed action.
Precisely,
`fixedJacquetMap_surjective_and_eventuallyStable_of_finite_coefficients`
concludes both surjectivity of the actual fixed-vector quotient and
`EventuallyStable (compressedAction ρ hρ K hK g)`. The latter is
`∃ n : ℕ, 0 < n ∧ Stable (compressedAction ρ hρ K hK g ^ n)`;
`Stable` includes both the kernel and range square equalities.
This exponent can depend on the supplied representation and coefficient
modules.

These coefficient finiteness and compatibility assumptions are explicit
inputs, to be verified on the actual universal representation families of
VI.9.2. They are not asserted for every smooth representation. This module
does not prove the host task's representation-uniform stabilization theorem.
The internal re-expression over an arbitrary commutative coefficient ring is
derived scope, rather than a literal restatement of Renard's complex-algebra
conventions.
