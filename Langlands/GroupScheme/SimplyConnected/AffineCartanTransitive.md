# Vertex-transitive affine extensions of Cartan matrices are of type `A`

This module proves a combinatorial fact about integer matrices and applies it to the
actual Cartan pairings `d.cartan` of a Tits-index datum `d : TitsIndexData G`. It
contains no statement about groups, buildings or local fields. Every result in it is
proved, with the standard axioms only.

## Provenance

The result is internal. It isolates the combinatorial step in the proof of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Theorem 10.3.1 (printed
p. 392 / PDF p. 423; source `kaletha-prasad-2023-bruhat-tits-new-approach`). There the
Galois group acts transitively on the basis `Δ` of an affine root system, and
Proposition 6.4.8, the description of irreducible affine root systems, shows that the
system is of type `A_n`. The Lean argument below does not use that list. It works
directly with an integer matrix that has a positive kernel vector and a
vertex-transitive automorphism group. The matrix hypotheses do not mention affine root
systems or the building. How such a matrix arises for an anisotropic group is the job
of the separate building-input statement that consumes this module.

## Main results

### `AffineCartan.exists_equiv_cartanA_of_transitive`

Let `ι` be a finite type and `B : Matrix (Option ι) (Option ι) ℤ`, where `none` is
one extra vertex. Assume:

* `B i i = 2` for every `i`, `B i j ≤ 0` for `i ≠ j`, and `B i j = 0 → B j i = 0`;
* some `m : Option ι → ℤ` with every `m i > 0` satisfies `Matrix.vecMul m B = 0`
  (`m ᵥ* B = 0`, that is `∑ i, m i * B i j = 0` for every `j`: a left kernel vector);
* for all `i j` there is a permutation `σ` of `Option ι` with
  `B (σ k) (σ l) = B k l` for all `k l` and `σ i = j`;
* the principal submatrix `A = B.submatrix some some` kills no nonzero integer vector.

Then `ι` is nonempty, and there are `n > 0` and `e : ι ≃ Fin n` with
`B (some a) (some b) = CartanMatrix.A n (e a) (e b)` for all `a b`.

Proof:

1. **Row and column sums vanish.** Each row sum `∑ j, B i j` equals the row sum at
   `none`: reindex the sum by an automorphism `σ` with `σ none = i`. Column sums are
   constant in the same way. Pairing the rows with `m` gives
   `0 = ∑ j, ∑ i, m i * B i j = (∑ i, m i) * (row sum)`, and `∑ m > 0`, so every row
   sum is `0`. The total sum is then `0`, and it equals `card (Option ι)` times the
   common column sum, so every column sum is `0` too.
2. **Properties of `A`.** Write `s a = ∑ b, A a b`.
   * Splitting off the `none` column of the row of `some a` gives `s a = -B (some a) none ≥ 0`.
   * The column of `none` gives `∑ a, s a = B none none = 2`.
   * Let `T` be a set of vertices that is closed (`a ∈ T` and `A a b ≠ 0` imply `b ∈ T`)
     and has `s = 0` on `T`. Then `A` kills the indicator vector of `T`, by symmetric
     support, so `T = ∅` by nondegeneracy.
3. **Off-diagonal entries of `A` are `0` or `-1`.** The off-diagonal entries of each row
   of `B` are nonpositive and add up to `-2`, so each one is at least `-2`. Suppose
   `B (some a) (some b) = -2`. Then that entry is the only nonzero off-diagonal entry
   of its row. The column sum at `some a` forces `B (some b) (some a) = -2`, so the
   same holds for the row of `some b`. Then `{a, b}` is a closed set with `s = 0` on
   it, and step 2 rules that out. Since `A a b = 0 ↔ A b a = 0`, it follows that `A`
   is symmetric.
4. **`exists_equiv_cartanA_of_path`** turns these properties into the renumbering `e`,
   with `n = card ι`.

### `AffineCartan.exists_equiv_cartanA_of_path`

Let `ι` have `r + 1` elements and let `A : Matrix ι ι ℤ` be symmetric, with diagonal
`2`, off-diagonal entries in `{0, -1}`, row sums `s a ≥ 0` with `∑ a, s a = 2`, and
no nonempty closed set on which every row sum is `0`. Then some `e : ι ≃ Fin (r + 1)`
satisfies `A a b = CartanMatrix.A (r + 1) (e a) (e b)`.

The proof is by induction on `r`. For `r = 0` both sides are `2`. In the inductive
step:

* Choose `a` with `s a > 0`. It has a neighbour: otherwise the other vertices would
  form a nonempty closed set on which every row sum is `0`. It has only one
  neighbour `b`, because two neighbours would make `s a ≤ 0`. So `s a = 1`.
* Deleting `a` (the subtype `{x // x ≠ a}`) preserves every hypothesis. The total row
  sum stays `2`. Any closed set of the smaller matrix with zero row sums omits `b`,
  whose row sum went up by one, so it is closed in `A` and therefore empty.
* The induction hypothesis numbers the remaining vertices.
* The new row sum at `b` is positive. An interior row of `CartanMatrix.A` sums to `0`
  (`cartanA_rowSum_eq_zero`), so `b` sits at an end of the numbering. If necessary,
  `Fin.revPerm` (see `cartanA_rev`) moves it to the last place.
* Finally `a ↦ Fin.last (r + 1)` and `x ↦ castSucc (e' x)` define a bijection
  `ι → Fin (r + 2)`, and the entries are compared case by case (`cartanA_castSucc`,
  `cartanA_last_castSucc`, `cartanA_symm`).

### `TitsIndexData.cartan_mulVec_eq_zero`

If `(Matrix.of d.cartan).mulVec v = 0` for `v : d.Vertex → ℤ`, then `v = 0`. Here
`d.cartan a b = ⟨α_a, α_b^∨⟩` for the root datum `d.pinning.rootDatum` and its base
`d.pinning.base`. The Library theorem
`Langlands.RootDatum.DominantMultiple.cartan_det_ne_zero` says that the integral
Cartan matrix `Matrix.of fun j k => ⟨α_j, α_k^∨⟩` of a base of a root datum has
nonzero determinant. That matrix is `Matrix.of d.cartan` entry by entry. Since `ℤ`
has no zero divisors, Mathlib's `Matrix.eq_zero_of_mulVec_eq_zero` turns the nonzero
determinant into `v = 0`.

Mathlib's `RootPairing.Base.cartanMatrix_nondegenerate` is not used. It assumes that
the roots span the whole lattice, which fails for the actual character lattice in
general (already for `SL₂`).

### `TitsIndexData.exists_equiv_cartanA_of_transitive_extension`

Let `B : Matrix (Option d.Vertex) (Option d.Vertex) ℤ` satisfy:

* `B (some a) (some b) = d.cartan a b` and `B none none = 2`;
* `B i j ≤ 0` for `i ≠ j`, and `B i j = 0 → B j i = 0`;
* some `m` with every `m i > 0` satisfies `Matrix.vecMul m B = 0`;
* for all `i j` some permutation `σ` of `Option d.Vertex` with
  `B (σ k) (σ l) = B k l` for all `k l` satisfies `σ i = j`.

Then `∃ n, 0 < n ∧ ∃ e : d.Vertex ≃ Fin n, ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b)`.
This is the conclusion of `LocalAnisotropicTypeAStatement`. The diagonal entries
`d.cartan a a = 2` come from `RootPairing.pairing_same`, and nondegeneracy comes from
`cartan_mulVec_eq_zero`. The proof then applies `exists_equiv_cartanA_of_transitive`.

## Scope

The hypotheses ask for one positive kernel vector only, on the left. Positivity is
used only through `∑ i, m i ≠ 0`. A vertex-transitive automorphism group is what the
argument needs, so a transitive action of some other group, such as a Galois group,
through automorphisms of `B` is enough. Nothing here shows that such a `B` exists for
any group scheme.
