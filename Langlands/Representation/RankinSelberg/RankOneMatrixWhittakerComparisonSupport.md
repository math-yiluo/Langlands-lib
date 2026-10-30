# Support of model functions along the rank-one embedding

This module is a helper for the positive-rank branch (`n = m + 1`) of the
published statement
`Langlands.RankinSelberg.RankOneMatrixWhittakerComparisonStatement`. There `σ`
acts on `GL(m + 1 + 1)`. Take a model function `W` of a standard functional
`ℓ`. The module proves that `W` vanishes at
`rankOneEmbedding m g = diag(det g, 1, …, 1)` unless `det g` lies in one
additive lattice `π^(-a) O`. The lattice depends on `W` but not on `g`.

This is a derived helper. It is not a statement from the literature. It is the
usual first step in the convergence of Whittaker integrals: a Whittaker function
on the torus vanishes when the torus coordinate is too large. The module does
not compare value sets and does not assemble the full statement. It reuses the
unipotent subgroup `x ↦ 1 + x E₀₁` of the helper module
`RankOneMatrixWhittakerComparisonCutoff`.

## Covariance along the embedded `GL₁`

`glModelFunction_rankOneEmbedding_mul_cutoffUnipotent ψ σ ℓ w g x` holds over
any topological field `F`. It states

```text
glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g * rankOneCutoffUnipotent m x)
  = ψ (det g * x) * glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g),
```

with `ψ` read through `ψ.complex`. The proof rewrites the left argument with
`rankOneEmbedding_mul_cutoffUnipotent` as
`(1 + det g · x E₀₁) · diag(det g, 1, …, 1)`. Then it applies the published
Whittaker covariance `glModelFunction_equivariance` to the unipotent element
`1 + det g · x E₀₁`. The value of the standard character there is
`ψ(det g · x)` (`standardCharacter_rankOneCutoffUnipotent`).

## The support bound

`exists_rankOneEmbedding_support T ψ σ` takes a `PadicField` `F` and any
topological data `T` on `F.Carrier`. The topology on `F.Carrier` is that of `T`,
and `ψ` is a unitary additive character for this topology. The conclusion is

```text
IsSmooth σ → ∀ ℓ w, ∃ a : ℤ, ∀ g : GL(0 + 1),
  glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) ≠ 0 →
    det g ∈ T.additiveLattice a.
```

Here `T.additiveLattice a` is `{x | v(x) ≤ exp a}`, that is `π^(-a) O`. The
positive-rank branch uses `T = F.canonicalTopologicalData`.

The proof runs as follows.

1. The published `glModel_isSmooth` says that the model representation is smooth
   when `σ` is. So the model vector `w` is fixed by an open subgroup `K` of
   `GL(m + 1 + 1)`.
2. The map `x ↦ 1 + x E₀₁` is continuous (`continuous_transvectionUnit`), so
   the preimage of `K` is open. It contains `0`, because `1 + 0 · E₀₁ = 1`
   (`transvectionUnit_zero`). The published
   `exists_additiveLattice_subset` gives `c` with `π^(-c) O` inside this
   preimage.
3. Let `g` satisfy `W(diag(det g, 1, …, 1)) ≠ 0`, and let `x ∈ π^(-c) O`. Then
   `1 + x E₀₁` lies in `K` and fixes `w`, so right translation by it does not
   change `W` (`glModelFunction_translate`). The covariance lemma gives
   `W(h) = ψ(det g · x) W(h)` at `h = diag(det g, 1, …, 1)`. Since `W(h) ≠ 0`,
   `ψ(det g · x) = 1`.
4. So `x ↦ ψ(det g · x)` is trivial on `π^(-c) O`. The published
   `mem_additiveLattice_of_forall_mul_eq_one` (module
   `ZeroRowLastRowCutoffProof`) then puts `det g` in `π^(c - n(ψ)) O`. Here
   `n(ψ)` is the additive conductor `T.additiveConductor ψ`. So the bound holds
   with `a = n(ψ) - c`.
