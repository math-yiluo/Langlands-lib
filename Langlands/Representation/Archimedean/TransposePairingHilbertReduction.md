# Restriction of genuine smooth Hilbert pairings

This derived comparison uses the published dense restriction argument in
`TransposePairingRestriction` with the genuine word-derivative carrier and
the explicit globalization and pairing predicates in `SmoothHilbert`.
It proves conditional implications, rather than either analytic existence
statement or the unconditional algebraic pairing statement.

`restrictSmoothHilbertPairing` constructs the explicit complex bilinear
form on the algebraic carrier by restricting both arguments along the
chosen compact-finite realization. Its value at `y, x` is
`B(j(y), j(x))`, where `j` is `smoothHilbertGlobalizationMap`.

For a complex inner product space `H`, a bounded-operator action `R` of
actual `GL_n(F)`, and an algebraic identification `e` with all compact-finite
smooth vectors, `isDenseWeakGLRealization_of_smoothHilbertGlobalization`
compares the two existing interfaces. The realization map is injective
because it is `e` followed by submodule inclusion. Density and compact
equivariance are the corresponding globalization clauses.

For the scalar derivative clause, a complex linear functional continuous
for the genuine derivative topology is bundled as a continuous linear map.
The globalization's exponential derivative property applies to that map
and to the realized vector. The two actual exponential curves have the
same matrix and inverse. The compatibility with the genuine first
derivative then identifies the scalar derivative with the image of
`π(1 ⊗ X)`. Thus every functional required by `IsDenseWeakGLRealization`
is tested, including functionals not continuous for the Hilbert norm.

`hasNonzeroTransposeGKPairing_of_smoothHilbertGlobalization` applies
the invariance and nonvanishing lemmas of `TransposePairingRestriction`
to this explicit form. The ambient
bilinear form is separately continuous and nonzero by the smooth pairing
predicate; density preserves nonvanishing on restriction. Compact
equivariance and scalar differentiation supply the exact compact and
complexified real Lie invariance. This comparison accepts a possibly
incomplete inner product space, since its explicit hypotheses already
contain every density and derivative fact it uses.

The final implications `realTransposePairing_of_hilbert` and
`complexTransposePairing_of_hilbert` take the respective Hilbert
globalization and smooth pairing statements as premises. Their
globalization conclusions supply a complete Hilbert space in the same
universe as the algebraic carrier. Applying the smooth pairing statement
to that representation and restricting gives the exact corresponding
algebraic target. `archimedeanTransposePairing_of_hilbert` combines these
two implications without changing the free carrier universe, compact
involution, or underlying real matrix Lie algebra.

The provenance is internal composition of these existing interfaces.
The analytic prerequisites were formulated from the corrected
Getz–Hahn Section 4.4 globalization discussion and Aizenbud–Gourevitch
Theorem 8.2.1; their paired Markdown records the original-source and
category comparisons. No globalization, character rigidity,
Fréchet completeness, moderate growth, or smooth contragredient
existence theorem is proved here.
