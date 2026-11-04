# Fixed vectors from reduced-translation exhaustion

Authors: Worker 1450 (Lean proof and first Markdown draft); Worker 1411
(Markdown revision and submission).

This module proves the implication

```
isMatrixUnipotent_of_isLocallyConilpotent :
  IsLocallyConilpotent k B → IsMatrixUnipotent k B
```

for a field `k` and a `k`-bialgebra `B` (`[Ring B]`, `[Bialgebra k B]`) in
arbitrary universes. It is one half of the criterion
`MatrixUnipotenceConilpotenceStatement`, assembled in
[`CriterionProof`](CriterionProof.md). It imports the published module
`CoalgebraUnipotence.Quotient` for the level lemmas `mem_reducedLevel_zero`,
`mem_reducedLevel_succ` and `reducedLevel_mono`, and uses
`AffineLinearEmbedding.rightAct` (`b ↦ ∑ f (b₂) • b₁` for
`comul b = ∑ b₁ ⊗ b₂`) unchanged. No finiteness hypothesis on `B` is used.

## Elements killed by all reduced translations

`eq_counit_smul_one_of_reduced_annihilation` states that if
`f b = 0` for every functional `f : Module.Dual k B` with `f 1 = 0`, then
`b = counit b • 1`. Since `k` is a field, an element of `B` is zero once
every functional vanishes on it (`Module.forall_dual_apply_eq_zero_iff`).
For an arbitrary functional `g`, the functional `g - g 1 • counit` vanishes
at `1` because `counit 1 = 1`, so by hypothesis it kills `b`; that is,
`g b - g 1 * counit b = 0`, which is `g (b - counit b • 1) = 0`.

## Coefficient vectors

For a matrix `a : Matrix (Fin n) (Fin n) B` and a vector `v : Fin n → k`,
`coefficientVector a v` is the vector `i ↦ ∑ j, v j • a i j` in `B`.
Suppose `a` is a coefficient matrix (`IsCoefficientMatrix`):
`comul (a i j) = ∑ l, a i l ⊗ₜ a l j` and `counit (a i j)` is the
`(i, j)` entry of the identity matrix.

- `counit_coefficientVector`: `counit (coefficientVector a v i) = v i`, by
  linearity and the counit law.
- `rightAct_coefficientVector`: for every functional `f`,

  ```
  rightAct f (coefficientVector a v i) =
    coefficientVector a (fun j => f (coefficientVector a v j)) i.
  ```

  The comultiplication law gives `rightAct f (a i j) = ∑ l, f (a l j) • a i l`.
  Substituting this, exchanging the two finite sums and collecting the scalars
  `∑ j, v j * f (a l j) = f (coefficientVector a v l)` yields the identity.
  Thus right translation by `f` sends the coefficient vector of `v` to the
  coefficient vector of `j ↦ f (coefficientVector a v j)`.

## The implication

Assume `IsLocallyConilpotent k B`, and let `n > 0` and `a` be a coefficient
matrix of size `n`. For a level `m`, let `P m` say that some nonzero
`v : Fin n → k` has all its coefficient entries `coefficientVector a v i` in
`reducedLevel k B m`.

1. Some `P m` holds. Take the constant vector `v = 1`, which is nonzero
   because `n > 0`. Each of its finitely many coefficient entries lies in some
   level by exhaustion, hence all lie in the supremum of these levels by
   `reducedLevel_mono`.
2. Let `m₀` be the least `m` with `P m` (`Nat.find`), with witness `v ≠ 0`.
   Then `m₀ ≠ 0`: level `0` is `⊥`, so all entries would vanish, and applying
   the counit (`counit_coefficientVector`) would give `v = 0`. Write
   `m₀ = m + 1`.
3. Let `f` be a functional with `f 1 = 0`, and put
   `w = (j ↦ f (coefficientVector a v j))`. By `mem_reducedLevel_succ`, each
   `rightAct f (coefficientVector a v i)` lies in level `m`, and by
   `rightAct_coefficientVector` this element is `coefficientVector a w i`.
   If `w` were nonzero it would witness `P m`, contradicting minimality of
   `m₀ = m + 1`. Hence `w = 0`: every functional vanishing at `1` kills every
   entry `coefficientVector a v i`.
4. By the lemma of the previous section and `counit_coefficientVector`,
   `coefficientVector a v i = v i • 1` for every `i`, i.e.
   `∑ j, v j • a i j = v i • 1`. So `v` is the required nonzero fixed vector.

## Provenance

This is an internal algebraic consequence of the definitions in
`CoalgebraUnipotence.Definitions`; no literature assertion is assumed and
no group-scheme comparison is used. `Statements.md` records how the criterion
is motivated by Milne's Theorem 14.5; the argument above is not taken from
Milne.
