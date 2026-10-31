# Determinant-weighted compact Whittaker synthesis

This internal helper derives determinant-weighted synthesis from actual compact
character synthesis. It represents every compact standard-Whittaker function by
one full-matrix Schwartz–Bruhat test, using the actual unipotent Haar integral.
It is a prerequisite for the matrix functional-equation comparison: it proves
neither the Fourier companion identity nor the gamma comparison.

For a topological field `K`, an absolute value `abv` satisfying
`Shahidi.IsOpenNormOne abv`, a size `n + 1`, a scalar character `χ` of the upper
unipotent subgroup, and `s : ℂ`, `weightedCompactFunction` is the complex-linear
map on actual `Induction.CompactFunctions` given by

```text
f(g) ↦ determinantWeight abv g (-s) * f(g).
```

It specializes the published `Induction.compactCharacterMultiply`. The identity
`determinantPower_upperUnipotent` follows from the determinant-one theorem for
the actual upper-unipotent subgroup. Thus multiplication preserves precisely
the same inducing character. The open-kernel theorem for determinant powers
preserves smoothness; the existing multiplier also preserves compact projected
support. No compactness of the support on the whole group is substituted for
compactness modulo the subgroup.

The main theorem `exists_weighted_matrix_whittaker_integral` uses a canonical
`F : PadicField p`, every unitary additive character `ψ`, every `n : ℕ`,
every complex `s`, and every actual compact induced function for
`standardCharacter ψ n`. It produces a single Schwartz–Bruhat function `Φ` on
all `(n + 1) × (n + 1)` matrices such that, for every actual group element `g`,
the literal integrand

```text
standardCharacter ψ n (u)^(-1) * Φ((u*g).val)
```

is Bochner integrable with respect to `unipotentHaar F.Carrier n`, and

```text
f(g) = determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s
       * ∫ u, standardCharacter ψ n (u)^(-1) * Φ((u*g).val).
```

The integral uses that same Haar measure. The function is chosen once before
the two universal quantifiers over `g`. Size one (`n = 0`) is included.
There is no character-conductor, self-duality, quotient-measure,
representation-theoretic or convergence assumption in addition to the
displayed input function and field data.

The proof applies `exists_matrix_characterOrbitIntegral_eq` to
`weightedCompactFunction ... f`. The canonical compact-open neighborhood basis
on the general linear group supplies its basis hypothesis. Closedness of the
actual unipotent subgroup, continuity of the standard character, and the Haar
and right-invariance instances of the actual unipotent measure supply its
remaining assumptions. The canonical normalized absolute value has open
norm-one subgroup. Finally, `Shahidi.determinantPower_neg` identifies the
negative-exponent character with the inverse; the two nonzero determinant
weights multiply to one. This proves the equality, while integrability is
inherited independently from matrix synthesis.

The provenance is internal derivation from the imported multiplier, determinant
characters, compact-open geometry and actual matrix synthesis. No external
Fourier identity or unproved matrix-to-rank-one comparison enters the proof.
