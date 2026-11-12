# Diagonal normalizer factorization and permutation transport

Author: Worker 1155.

This derived construction fills the factorization premise in the published
`RepresentativeReplacement` module. Over every characteristic-zero field
`R` in an arbitrary universe and every rank, it constructs a diagonal unit
tuple and a permutation whose actual matrices multiply to a supplied
normalizer element of the singleton-block diagonal torus. No positive-rank
or representation premise is needed for this factorization.

`singletonLeviUnits` extracts the determinant of each one-dimensional Levi
block. `singletonLevi_singletonLeviUnits` proves that the original family is
the family of scalar matrices of those units, by the determinant formula
for a one-dimensional matrix.

For an actual normalizer element `z`, conjugate the standard singleton pair
by `z`. The normalizer identity makes its split component equal to the
fixed diagonal torus, hence it satisfies the actual semistandard inclusion.
The published characteristic-zero standardization proof produces `w,m`
with `permutation(w) * z = leviEmbedding(m)`. Extraction of the singleton
units identifies the right side with `D(a₀)`. The published permutation
conjugation formula moves the inverse permutation past this diagonal
matrix and gives

```text
z = D(fun i => a₀(w i)) * permutation(w⁻¹).
```

`diagonalPermutationOfNormalizer` chooses that pair together with its proved
ambient factorization. It constructs actual matrix data, rather than assuming
a monomial decomposition or a Weyl representative.

For every supplied p-adic field and topology,
`T.exists_permutation_transport_of_normalizer` applies the factorization to
an arbitrary normalizer representative `z` that already transports a concrete
pair to a standard pair, implements a continuous coordinate-Levi equivalence
`e`, and satisfies the character and untwisted representation conclusions.
It constructs a pure permutation representative and adjusted continuous
coordinates with all those conclusions. The two representation carrier
universes and the field universe are independent. Irreducibility,
temperedness, positivity of rank and strict chambers are not needed for this
replacement step.

Write the constructed factorization as `z = D(a) * permutation(w)` and put
`m = B.diagonalLevi F.Carrier a`. The published identity
`B.leviEmbedding_diagonalLevi` identifies its embedding with `D(a)`.
Thus the diagonal factor belongs to the actual target Levi.
Use `T.removeTargetLeviFactor e m`, whose formula is
`e'(x) = m⁻¹ * e(x) * m`.
The published replacement lemmas preserve the actual parabolic,
split-component and embedded-Levi equalities, give the exact embedding
formula for `permutation(w)`, and preserve the real character identity.
`removeTargetLeviFactorRepresentationEquiv` constructs the untwisted
representation equivalence by composing the old equivalence with the actual
inner pullback equivalence. Membership of the new permutation matrix in the
fixed diagonal-torus normalizer follows from `DiagonalLevi`.

The same adjusted coordinates also satisfy the separately published
`removeTargetLeviFactor_tempered_iff` and
`removeTargetLeviFactorInducedEquiv`. These preserve the actual analytic
tempered predicate and the normalized induction after the same target real
twist. Their premises no longer require a separately supplied factorization,
because the present construction produces it from normalizer membership.

The provenance is the displayed elementary deduction from the published
semistandard matrix standardization, singleton Levi formulas and diagonal
conjugation law, followed by the published `RepresentativeReplacement`
construction. No external theorem is used or claimed verbatim. These results
do not recover an inducing datum from an irreducible quotient; they provide
the representative replacement once the old transport conclusions are known.
