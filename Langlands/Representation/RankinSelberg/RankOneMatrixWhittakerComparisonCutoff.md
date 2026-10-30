# Fourier cutoff along the rank-one embedding

This module is a helper for the positive-rank branch (`n = m + 1`) of the
published statement
`Langlands.RankinSelberg.RankOneMatrixWhittakerComparisonStatement`. There `σ`
acts on `GL(m + 1 + 1)`. The module proves the following. Take a model function
`W` of a standard functional `ℓ` and a Schwartz–Bruhat function `φ` on `F`. Then
some model function `W'` of the same `ℓ` agrees with `φ(det g) · W` on the
embedded group `GL₁`, that is, at the matrices
`rankOneEmbedding m g = diag(det g, 1, …, 1)`.

This is a derived helper. It is not a statement from the literature. The proof
is the one-coordinate version of the Fourier cutoff in the Library's
`RankOneExtensionScalarCutoffProof`: smear `W` on the right along a one-parameter
unipotent subgroup against a Fourier preimage of `φ`. The module does not
compare value sets and does not assemble the full statement.

## The unipotent subgroup

- `rankOneCutoff_index_ne m`: the indices `0` and `1` of `Fin (m + 1 + 1)` are
  different.
- `rankOneCutoffUnipotent m x` is the published transvection
  `transvectionUnit 0 1 _ x`, that is, the matrix `1 + x E₀₁` in
  `GL(m + 1 + 1)`. `rankOneCutoffUnipotent_apply` gives its entries:
  `δᵢⱼ + (x if i = 0 and j = 1, else 0)`.
- `rankOneCutoffUnipotent_mem`: `1 + x E₀₁` lies in `upperUnipotent (m + 1 + 1) F`.
- `rankOneEmbedding_mul_cutoffUnipotent`: for `g` in `GL(0 + 1)`,

  ```text
  rankOneEmbedding m g * rankOneCutoffUnipotent m x
    = rankOneCutoffUnipotent m (det g * x) * rankOneEmbedding m g.
  ```

  The proof compares entries. Both sides are a diagonal matrix times a
  transvection (`Matrix.diagonal_mul`, `Matrix.mul_diagonal`). Only entry
  `(0, 1)` is off the diagonal, and there the diagonal entries are `det g` and
  `1`.
- `standardCharacter_rankOneCutoffUnipotent`: the published standard character
  `standardCharacter ψ (m + 1)` takes the value `ψ(x)` on `1 + x E₀₁`. The
  character is `ψ` applied to the sum of the superdiagonal entries
  (`standardCharacter_apply`). Of these entries only entry `(0, 1)` is nonzero,
  and it equals `x`.

## The cutoff for a self-dual measure

`exists_rankOneCutoff_of_isSelfDual ψ μ hμ σ hσ ℓ w φ` holds over any
topological field `F` that is locally compact, Hausdorff and totally
disconnected, with a Borel measurable structure. It assumes that the additive
Haar measure `μ` is self-dual for `ψ` (`IsSelfDual ψ μ`) and that `σ` is smooth.
Its conclusion is

```text
∃ w', ∀ g : GL(0 + 1),
  glModelFunction ψ (m + 1) σ ℓ w' (rankOneEmbedding m g)
    = φ (det g) * glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g).
```

The proof runs as follows.

1. Let `φ⁻(x) = φ(-x)`; this is a Schwartz–Bruhat function, the pullback of
   `φ` along negation. The published `scalarFourierClosure` gives a
   Schwartz–Bruhat function `κ` equal to the Fourier transform of `φ⁻`.
   Self-duality of `μ` says that the Fourier integral of the Fourier transform
   of `φ⁻` is `φ⁻(-b) = φ(b)`. Hence `φ(b) = ∫ ψ(x b) κ(x) dμ(x)` for every `b`.
2. The published `Smearing.exists_coefficient_average`, applied to the
   continuous map `x ↦ 1 + x E₀₁` (`continuous_transvectionUnit`) and to `κ`,
   gives a model vector `w'` with
   `W'(h) = ∫ κ(x) W(h (1 + x E₀₁)) dμ(x)` for every `h`, where `W` and `W'`
   are the model functions of `w` and `w'`.
3. Take `h = diag(det g, 1, …, 1)`. By `rankOneEmbedding_mul_cutoffUnipotent`,
   Whittaker covariance of `W` and `standardCharacter_rankOneCutoffUnipotent`,
   `W(h (1 + x E₀₁)) = ψ(x det g) W(h)`. Pulling the constant `W(h)` out of the
   integral (`integral_mul_const`) and using step 1 at `b = det g` gives
   `W'(h) = φ(det g) W(h)`.

## The p-adic cutoff

`exists_rankOneCutoff F ψ σ` is the form used by the positive-rank branch. Here
`F` is a `PadicField`. The topology on `F.Carrier` is that of
`F.canonicalTopologicalData`, and `ψ` is a unitary additive character for this
topology. The conclusion is

```text
IsSmooth σ → ∀ ℓ w φ, ∃ w', ∀ g : GL(0 + 1),
  glModelFunction ψ (m + 1) σ ℓ w' (rankOneEmbedding m g)
    = φ (det g) * glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g).
```

The proof installs the valuative relation, the local-field certificate, the
uniform structure, the Borel σ-algebra and the Hausdorff property of the
canonical topology. These are the instances under which the published
`padicSelfDualMeasureExists` is stated. That theorem gives total
disconnectedness and a self-dual measure `μ` for `ψ`. The self-dual cutoff then
applies.
