# Reduced-translation exhaustion from fixed vectors

Authors: Worker 1450 (Lean proof and first Markdown draft); Worker 1411
(Markdown revision and submission).

This module proves the implication

```
isLocallyConilpotent_of_isMatrixUnipotent :
  IsMatrixUnipotent k B → IsLocallyConilpotent k B
```

for a field `k` and a `k`-bialgebra `B` (`[Ring B]`, `[Bialgebra k B]`) in
arbitrary universes, with no finiteness hypothesis on `B`. It is the other
half of the criterion assembled in [`CriterionProof`](CriterionProof.md). It
imports [`MatrixFromConilpotence`](MatrixFromConilpotence.md) (and through
it the published `Quotient` level lemmas) and uses from the published
`AffineLinearEmbedding.Comodule` module the translations `rightAct f`
(`b ↦ ∑ f (b₂) • b₁`) and `leftAct φ` (`b ↦ ∑ φ (b₁) • b₂`) for
`comul b = ∑ b₁ ⊗ b₂`, together with the lemmas `apply_leftAct`
(`g (leftAct φ b) = φ (rightAct g b)`), `rightAct_leftAct` (left and right
translations commute), `rightAct_rightAct` (composition of right
translations), `rightAct_counit`, `tensor_ext` (tensors in `B ⊗ B` are
separated by contracting the second factor with functionals) and
`exists_matrix_coefficients`.

## Stability of the levels

- `rightAct_one` (a `simp` lemma): `rightAct f 1 = f 1 • 1`, since
  `comul 1 = 1 ⊗ 1`.
- `rightAct_mem_reducedLevel n g hb`: every level `reducedLevel k B n` is
  stable under every right translation `rightAct g`, for an arbitrary
  functional `g` (not only those vanishing at `1`). Level `0` is `⊥`. For
  level `n + 1` and `f` with `f 1 = 0`, `rightAct_rightAct` gives
  `rightAct f (rightAct g b) = rightAct (f ∘ₗ rightAct g) b`, and the
  functional `f ∘ₗ rightAct g` vanishes at `1` by `rightAct_one`
  (its value is `g 1 * f 1 = 0`). So the hypothesis
  `b ∈ reducedLevel k B (n + 1)` applies directly.

## Fixed vectors in finite quotients of stable subspaces

`exists_fixed_mod_of_isMatrixUnipotent` takes `IsMatrixUnipotent k B`, a
subspace `W ≤ B` with `rightAct f w ∈ W` for all functionals `f` and all
`w ∈ W`, a nontrivial finite-dimensional `k`-vector space `V`, and a
surjective linear map `q : W → V` whose kernel is stable under all right
translations. It produces `w ∈ W` with `q w ≠ 0` such that
`q (rightAct f w) = 0` for every `f` with `f 1 = 0`.

Proof. Let `n = finrank V > 0` and let `e` be a basis of `V` indexed by
`Fin n`. Choose a linear section `s` of `q` and a linear projection
`P : B → W` that restricts to the identity on `W`. The functionals
`φ i = e.coord i ∘ q ∘ P` on `B` satisfy `φ i w = e.coord i (q w)` for
`w ∈ W`. Define `M i j = leftAct (φ i) (s (e j))`.

1. If `w ∈ W` and `q w = 0`, then `leftAct (φ i) w = 0`: for every
   functional `g`, `g (leftAct (φ i) w) = φ i (rightAct g w)
   = e.coord i (q (rightAct g w)) = 0` by kernel stability, and functionals
   separate the points of `B`.
2. Hence, for `w ∈ W`, `leftAct (φ i) w = ∑ l, e.coord l (q w) • M i l`:
   `w - s (q w)` lies in the kernel of `q`, so `leftAct (φ i)` takes the same
   value on `w` and on `s (q w) = ∑ l, e.coord l (q w) • s (e l)`.
3. `e.coord i (q (rightAct g (s (e j)))) = g (M i j)` for every `g`, by
   `apply_leftAct`.
4. `M` is a coefficient matrix. For comultiplication, by `tensor_ext` it
   suffices to compare contractions with each functional `g` in the second
   factor. The contraction of `comul (M i j)` is
   `rightAct g (leftAct (φ i) (s (e j))) = leftAct (φ i) (rightAct g (s (e j)))`
   (`rightAct_leftAct`), which by steps 2 and 3 equals
   `∑ l, g (M l j) • M i l`, the contraction of `∑ l, M i l ⊗ₜ M l j`. For
   the counit, `counit (M i j) = φ i (rightAct counit (s (e j)))
   = φ i (s (e j)) = e.coord i (e j)`, the `(i, j)` entry of the identity
   matrix.
5. Matrix unipotence gives `v : Fin n → k`, `v ≠ 0`, with
   `∑ j, v j • M i j = v i • 1` for every `i`. Let `y = ∑ j, v j • e j`;
   its coordinates are `v`, so `y ≠ 0`. Take `w = s y`, so `q w = y ≠ 0`. For
   `f` with `f 1 = 0`, each coordinate of `q (rightAct f w)` is
   `e.coord i (q (rightAct f (s y))) = f (leftAct (φ i) (s y))
   = f (∑ j, v j • M i j) = f (v i • 1) = v i * f 1 = 0`.
   Hence `q (rightAct f w) = 0`.

## Finite stable subspaces lie in a level

`exists_reducedLevel_containing_finite_stable` states that, under
`IsMatrixUnipotent k B`, every finite-dimensional subspace `W` stable under
all right translations satisfies `W ≤ reducedLevel k B n` for some `n`.

Proof. The pullbacks `F n` of the levels to `W` form an increasing sequence
of subspaces of `W` (`reducedLevel_mono`). Since `W` is finite-dimensional,
hence Noetherian, the sequence stabilizes (`monotone_stabilizes_iff_noetherian`):
there is `n` with `F n = F (n + 1)`. Suppose `F n ≠ W`. Then the quotient
`W ⧸ F n` is nontrivial and finite-dimensional, and the kernel `F n` of the
quotient map is stable under right translations by
`rightAct_mem_reducedLevel`. The previous section gives `w ∈ W` outside
`F n` with `rightAct f w ∈ F n` for every `f` with `f 1 = 0`. By
`mem_reducedLevel_succ`, `w ∈ F (n + 1) = F n`, a contradiction. Therefore
`F n = W`, that is, `W ≤ reducedLevel k B n`.

## The implication

Given `b : B`, `exists_matrix_coefficients` applied to `{b}` gives a size `N`
and a coefficient matrix `M` of that size (in the sense of the two identities
of `IsCoefficientMatrix`) such that `b` lies in the span `W` of the entries
of `M`. This published theorem is proved in `AffineLinearEmbedding.Comodule`
for an arbitrary coalgebra over a field and is attributed there to Milne,
Proposition 4.7 and Theorem 4.9, for the regular comodule. The span `W` is
finite-dimensional. It is stable under every right translation, because
`rightAct f (M i j) = ∑ l, f (M l j) • M i l` by the comultiplication law.
The previous section puts `W`, and hence `b`, into some level.

## Provenance

The arguments are internal algebraic consequences of the coefficient-matrix
fixed-vector predicate of `CoalgebraUnipotence.Definitions`. They assume no
literature assertion beyond the published, proved theorem
`exists_matrix_coefficients`, and no group-scheme comparison or
coconnectedness theorem. `Statements.md` records how the criterion is
motivated by Milne's Theorem 14.5; this proof is not taken from Milne.
