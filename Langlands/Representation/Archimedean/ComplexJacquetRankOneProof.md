# The rank-one reordering of Jacquet exponents

Module `Langlands.Representation.Archimedean.ComplexJacquetRankOneProof`, namespace
`Langlands.Archimedean`, universe `uV` for the module carrier.

## Statement

```
theorem complexJacquetRankOne : ComplexJacquetRankOneStatement.{uV}
```

`ComplexJacquetRankOneStatement` is the Library statement of module
`Langlands.Representation.Archimedean.ComplexJacquetReduction`. Let `V` be an irreducible
admissible `(𝔤𝔩_n(ℂ), U(n))`-module, `ℓ` a nonzero Jacquet functional on `V` with exponents
`(a, b)` (`ℓ` vanishes on `𝔫V`, and `ℓ ∘ π(1 ⊗ E_kk) = a_k ℓ`, `ℓ ∘ π(1 ⊗ i E_kk) = b_k ℓ`),
and `j = i + 1` adjacent positions with `Re a_j + 2 < Re a_i`. Then there is a nonzero Jacquet
functional `ℓ'` with exponents `(a', b')` such that `a'_k = a_k` for `k ∉ {i, j}`,
`a'_i + a'_j = a_i + a_j` and `Re a'_i ≤ Re a'_j + 2`.

## Proof

The theorem is the composition of three implications and two proved inputs:

* `complexJacquetRankOneReduction` (Library, module `ComplexJacquetRankOneReduction`):
  `ComplexGLTwoJacquetOrderingStatement → ComplexJacquetRankOneStatement`, by restricting to the
  `GL_2(ℂ)` block at rows and columns `i, j`.
* `complexGLTwoJacquetOrderingReduction` (Library, module
  `ComplexGLTwoJacquetOrderingReduction`): `ComplexGLTwoMomentJacquetStatement` and
  `ComplexGLTwoMomentCompletenessStatement` imply `ComplexGLTwoJacquetOrderingStatement`. A
  nonzero Jacquet functional of a `(𝔤𝔩_2(ℂ), U(2))`-module gives, by Frobenius reciprocity, a
  map into a principal series `X(d)`; when `Re t_1 < Re t_0`, composing it with a moment
  `M_{i,j}` of minimal order `i + j` among those nonzero on the image yields a Jacquet
  functional with the reordered exponents.
* `complexGLTwoMomentJacquet : ComplexGLTwoMomentJacquetStatement` (module
  `ComplexGLTwoMomentJacquetProof`, with the integration-by-parts helper module
  `ComplexGLTwoMomentAnalysis`): the moments `M_{i,j} f = ∫_ℂ f(w n(z)) z^i z̄^j dz` converge for
  `i + j < 2 Re(t_0 - t_1)` and transform under the upper triangular Lie algebra by explicit
  formulas.
* `complexGLTwoMomentCompleteness : ComplexGLTwoMomentCompletenessStatement` (module
  `ComplexGLTwoMomentCompletenessProof`, with helper modules `ComplexGLTwoWirtinger`,
  `ComplexGLTwoNoncompactPicture`, `ComplexGLTwoNoncompactOperators`,
  `ComplexGLTwoHighestWeight`, `ComplexGLTwoWeylBound`, `ComplexGLTwoLadder`,
  `ComplexGLTwoRadial`): every nonzero `(𝔤, K)`-submodule of `X(d)` with `Re t_1 < Re t_0`
  contains a function with `M_{i,j} f ≠ 0` for some `i + j ≤ Re(t_0 - t_1)`.

The Lean proof term is

```
complexJacquetRankOneReduction.{uV}
  (complexGLTwoJacquetOrderingReduction.{uV} complexGLTwoMomentJacquet
    complexGLTwoMomentCompleteness)
```

Each helper module has its own Markdown file describing its proofs. The theorem uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.
