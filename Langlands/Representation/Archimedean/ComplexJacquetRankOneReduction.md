# Reduction of the rank-one reordering of Jacquet exponents to `GL_2(ℂ)`

Lean module: `Langlands.Representation.Archimedean.ComplexJacquetRankOneReduction`
(namespace `Langlands.Archimedean`, helpers in `Langlands.Archimedean.RankOneBlock`,
universe `uV` for the module carrier).

## Statement

```
def ComplexJacquetRankOneReductionStatement : Prop :=
  ComplexGLTwoJacquetOrderingStatement.{uV} → ComplexJacquetRankOneStatement.{uV}
```

`ComplexJacquetRankOneStatement` is the Library's rank-one reordering step
(module `Langlands.Representation.Archimedean.ComplexJacquetReduction`). Take an irreducible
admissible `(𝔤𝔩_n(ℂ), U(n))`-module `V`, a nonzero Jacquet functional `ℓ` with weight `(a, b)`,
and adjacent positions `j = i + 1` with `Re a_j + 2 < Re a_i`. The statement gives a nonzero Jacquet
functional `ℓ'` with weight `(a', b')`, where `a'_k = a_k` for `k ∉ {i, j}`,
`a'_i + a'_j = a_i + a_j` and `Re a'_i ≤ Re a'_j + 2`.

`ComplexGLTwoJacquetOrderingStatement` (module
`Langlands.Representation.Archimedean.ComplexGLTwoJacquetOrdering`) is the same conclusion for
`n = 2` at the positions `0, 1`. It holds for every `(𝔤𝔩_2(ℂ), U(2))`-module: irreducibility,
admissibility and the hypothesis `Re a_1 + 2 < Re a_0` are not assumed.

The theorem `complexJacquetRankOneReduction : ComplexJacquetRankOneReductionStatement.{uV}`
proves the implication. It is `RankOneBlock.complexJacquetRankOne_of_glTwo`. The proof never uses
the irreducibility or admissibility hypotheses of `ComplexJacquetRankOneStatement`, or the
hypothesis `Re a_j + 2 < Re a_i`.

## Provenance

This is our own reduction. Literature proofs of the reordering step (Wallach 1979, the minimality
argument of Lemma 5.13 with the parabolic Jacquet modules of 4.20-4.21 and 5.3) pass to the Levi
`GL_2(ℂ) × GL_1(ℂ)^{n-2}` of the parabolic with Levi block `{i, j}`. They need that the parabolic
Jacquet module of an admissible module is admissible. The argument below needs no admissibility.
It uses only a quotient of `V` on which `𝔤𝔩_2(ℂ)` acts through the block `{i, j}`. The input at
`GL_2(ℂ)` is the hypothesis-free statement `ComplexGLTwoJacquetOrderingStatement`.

## The construction

Fix `n`, the module `(V, ρ, π)`, the functional `ℓ` with weight `(a, b)`, and `j = i + 1`.

### Block embeddings (section `Block`, `Embedding`)

* `proj i j : Matrix (Fin 2) (Fin n) ℂ` has entries `1` at `(0, i)` and `(1, j)` and `0`
  elsewhere. `compl i j = 1 - projᵀ proj` is the diagonal projection onto the coordinates
  other than `i, j`.
* `blockMat i j X = projᵀ X proj` places a `2 × 2` matrix in rows and columns `i, j`.
  `blockUnit i j M = blockMat i j M + compl i j` completes it by the identity elsewhere.
* For `i ≠ j`, `proj projᵀ = 1`. Hence `blockMat` is multiplicative, `blockUnit` is
  multiplicative and unital, and both commute with `star`. They also satisfy
  `blockUnit M * blockMat X = blockMat (M X)`, `blockMat X * blockUnit M = blockMat (X M)`,
  and `blockMat (single p q c) = single (![i, j] p) (![i, j] q) c`.
* `blockLie hij : ℂ ⊗[ℝ] 𝔤𝔩_2(ℂ) →ₗ⁅ℂ⁆ ℂ ⊗[ℝ] 𝔤𝔩_n(ℂ)` is the base change of the `ℝ`-linear map
  `blockMat`, `c ⊗ X ↦ c ⊗ blockMat X`. It preserves brackets because `blockMat` preserves
  products.
* `blockUnitHom hij : U(2) →* U(n)` is `M ↦ blockUnit M`. It lands in `U(n)` because `blockUnit`
  commutes with `star` and is multiplicative and unital. It is continuous because it is built
  from matrix multiplication and addition.

### The subspace `S` (section `Support`, `Commute`, `Sub`)

* `InNP i j X` means `X a b = 0` whenever `b ≤ a` or `(a, b) = (i, j)`. These `X` form the
  nilradical `𝔫_P` of the parabolic with Levi block `{i, j}`, viewed in `𝔤𝔩_n(ℂ)`.
* `IsBlockDiag i j g` means that `g` is supported on the diagonal together with the
  `{i, j} × {i, j}` block. Identity matrices, `blockMat X` and `blockUnit M` are block-diagonal.
  For `j = i + 1`, `inNP_mul` shows `g X h ∈ 𝔫_P` for block-diagonal `g, h` and `X ∈ 𝔫_P`.
* `offSub π i j a b = S` is the complex span of
  - the vectors `π(1 ⊗ X) v` with `InNP i j X`;
  - the vectors `π(1 ⊗ E_kk) v - a_k v` and `π(1 ⊗ i E_kk) v - b_k v` for `k ∉ {i, j}`.
    Here `E_kk = Matrix.single k k 1` and `i E_kk = Matrix.single k k Complex.I`.
* `offSub_le_ker`: `S ⊆ ker ℓ`. The first family is killed because `𝔫_P` is strictly upper
  triangular. The second family is killed by the eigenvalue conditions on `ℓ`.
* `offSub_stable_blockLie`: `S` is stable under `π(blockLie x)`. For `Z = blockMat Y`,
  `[Z, X] ∈ 𝔫_P` for `X ∈ 𝔫_P` (from `inNP_mul`). Also `Z` commutes with `E_kk` and `i E_kk` for
  `k ∉ {i, j}`, since both products vanish. The Library lemma `complex_map_commutator` turns
  these matrix identities into identities between the operators `π(1 ⊗ ·)`.
* `offSub_stable_rho`: `S` is stable under `ρ(blockUnitHom g)`. This uses the fourth condition
  of `IsComplexGKModule`, `ρ(u) π(1 ⊗ X) ρ(u)⁻¹ = π(1 ⊗ u X u*)`. With `u = blockUnit g`,
  `u X u*` lies in `𝔫_P` for `X ∈ 𝔫_P`, and `u E_kk u* = E_kk` for `k ∉ {i, j}`.

### The `(𝔤𝔩_2(ℂ), U(2))`-module `W = V ⧸ S` (sections `Quotient`, `Module`)

* `quotRep` and `quotLieHom` pass a representation, and a Lie algebra action, to a quotient by a
  stable subspace.
* `blockRho` is `ρ ∘ blockUnitHom` on `W`. `blockPi` is `π ∘ blockLie` on `W`.
* `isComplexGKModule_block` proves `IsComplexGKModule 2 blockRho blockPi` by checking the four
  conditions on representatives `v`:
  1. `U(2)`-finiteness: the `U(2)`-orbit span of `[v]` is contained in the image in `W` of the
     finite-dimensional `U(n)`-orbit span of `v`.
  2. Continuity of `g ↦ λ(blockRho g [v])`: this is the continuity of `u ↦ (λ ∘ mkQ)(ρ u v)`
     composed with the continuous `blockUnitHom`.
  3. Derivatives along curves: if `γ` is a curve in `U(2)` with `γ 0 = 1` and entrywise derivative
     `X` at `0`, then `blockUnit ∘ γ` is a curve in `U(n)` with entrywise derivative `blockMat X`
     (`hasDerivAt_blockUnit`). Apply the condition for `V` to the functional `λ ∘ mkQ`.
  4. Conjugation: `blockUnit g * blockMat X * star (blockUnit g) = blockMat (g X g*)`.
* `isJacquet_block`: `ℓ` descends to `ℓ_W = S.liftQ ℓ`, a Jacquet functional on `W` with weight
  `(![a i, a j], ![b i, b j])`. A strictly upper triangular `2 × 2` matrix is `single 0 1 c`,
  and `blockMat (single 0 1 c) = single i j c` is strictly upper triangular in `𝔤𝔩_n` since
  `j = i + 1`. The diagonal conditions follow from
  `blockMat (single p p c) = single (![i, j] p) (![i, j] p) c`.

### Applying the `GL_2` statement and pulling back (`complexJacquetRankOne_of_glTwo`)

`ℓ_W ≠ 0` because `ℓ = ℓ_W ∘ mkQ`. The hypothesis `ComplexGLTwoJacquetOrderingStatement` applied to
`(W, blockRho, blockPi, ℓ_W)` gives a nonzero Jacquet functional `μ` on `W` with weight
`(a'', b'')`, where `a''_0 + a''_1 = a_i + a_j` and `Re a''_0 ≤ Re a''_1 + 2`. Put
`ℓ' = μ ∘ mkQ`, which is nonzero since `mkQ` is surjective. Put `a'_i = a''_0`, `a'_j = a''_1`,
`b'_i = b''_0`, `b'_j = b''_1`, and `a'_k = a_k`, `b'_k = b_k` for `k ∉ {i, j}`. Then:

* `ℓ'` kills `π(1 ⊗ X) v` for strictly upper triangular `X`. Write
  `X = (X - single i j (X i j)) + blockMat (single 0 1 (X i j))`. The first summand is in
  `𝔫_P`, so its image lies in `S = ker mkQ`. The second summand acts on `W` as
  `blockPi (1 ⊗ single 0 1 (X i j))`, which `μ` kills.
* For `k ∈ {i, j}` the eigenvalue conditions are those of `μ` at `0` or `1`, transported by
  `blockMat (single p p c) = single (![i, j] p) (![i, j] p) c`.
* For `k ∉ {i, j}`, `mkQ (π(1 ⊗ E_kk) v) = a_k mkQ v` and `mkQ (π(1 ⊗ i E_kk) v) = b_k mkQ v`
  by the definition of `S`.
* `a'_k = a_k` off `{i, j}`, `a'_i + a'_j = a_i + a_j`, and `Re a'_i ≤ Re a'_j + 2` follow
  from the corresponding facts for `a''`, using `i ≠ j`.

## Use

Combined with a proof of `ComplexGLTwoJacquetOrderingStatement`, `complexJacquetRankOneReduction`
proves `ComplexJacquetRankOneStatement` (Task 7066).

## References

* N. R. Wallach, *Representations of reductive Lie groups*, in *Automorphic forms,
  representations and L-functions* (Corvallis 1977), Proc. Sympos. Pure Math. 33, Part 1,
  AMS 1979, pp. 71-86: 4.20-4.21, 5.3 and Lemma 5.13 (the minimality argument whose rank-one
  step this reduction replaces).
