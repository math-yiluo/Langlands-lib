# Lattice maps preserving the type `D` roots are signed permutations

Author: Worker 1383, for Task 6507 (`f0045927-f50c-4853-9944-3c98c7ea5daf`), in collaboration
with Worker 74. This is a support module for the proof of
`SpecialOrthogonalAutomorphismStatement`. `TorusNormalization` uses it to turn an
automorphism of the diagonal torus of `SO_{2l}` that preserves the roots into a permutation
matrix. All declarations are in the namespace `Langlands.GroupScheme.OrthogonalMatrix`.

## Notation

Fix a type `l` with decidable equality. The Library supplies the following, all imported
through `OrthogonalMatrix.TypeD` (which imports `OrthogonalMatrix.Roots`).

- `weightCoord l : l ⊕ l → (l → ℤ)` sends `inl a` to `e_a = Pi.single a 1` and `inr a` to
  `-e_a = Pi.single a (-1)`. These are the weights of the diagonal torus of `O_{2l}` in
  coordinates. It is injective (`SymplecticMatrix.weightCoord_injective`).
- `index x` is `a` for `x = inl a` and for `x = inr a`. `Sum.swap` exchanges `inl a` and
  `inr a`, so `index x.swap = index x` and `weightCoord l x.swap = -weightCoord l x`.
- The roots of type `D_l` are the differences `w(x) - w(y)` with `index x ≠ index y`, where
  `w = weightCoord l` (`OrthogonalMatrix.mem_roots_iff` in `Roots`).

## Statements

- `weightCoord_swap_add x`: `w(swap x) + w(x) = 0`.
- `weightCoord_add_self_ne_zero x`: `w(x) + w(x) ≠ 0`.
- `index_eq_or_of_add_self (hab : index a ≠ index b) (hv : v + v = w a + w b + (w c + w d))`:
  then `index c = index a` or `index d = index a`.
- `signedRoot_half_sum_of_index_eq`: assume `index c = index a`, `index d = index b`,
  `w a + w b ≠ w c + w d`, `w a + w b + (w c + w d) ≠ 0` and `v + v = w a + w b + (w c + w d)`.
  Then `v = w z` for some `z`.
- `signedRoot_half_sum (hab : index a ≠ index b) h1 h2 hv`: the same conclusion
  `∃ z, v = w z` without the index hypotheses on `c` and `d`. Only `index a ≠ index b` is
  assumed, together with the same `h1`, `h2` and `hv`.
- `weightCoord_sub_eq_add x y`: `w x - w y = w x + w (swap y)`.
- `exists_map_weightCoord_eq [Nontrivial l] M hM hroot x`: here `M : (l → ℤ) →+ (l → ℤ)` is
  injective (`hM`). `hroot` says that `M` sends roots to roots: for all `x y` with
  `index x ≠ index y` there are `x' y'` with `index x' ≠ index y'` and
  `M (w x - w y) = w x' - w y'`. Then `M (w x) = w z` for some `z`.
- `exists_perm_map_weightCoord [Finite l] [Nontrivial l] M hM hroot`: under the same hypotheses
  there is a permutation `σ` of `l ⊕ l` with `σ (swap x) = swap (σ x)` for all `x` and
  `M (w x) = w (σ x)` for all `x`.

So the induced map on weights is a signed permutation of the `±e_a`. The hypothesis that `l`
has at least two elements is needed: for a single index there are no roots.

## Proofs

**Parity.** In `index_eq_or_of_add_self`, evaluate `hv` at `index a`. The left side is even.
On the right, `w a` contributes `±1` and `w b` contributes `0`. If neither `c` nor `d` had index
`index a`, the right side would be `±1`, which is odd. This is `omega` after `sgn_eq`.

**Half-sums.** In `signedRoot_half_sum_of_index_eq`, each of `c` and `d` is either the given
index-mate or its swap (`eq_or_eq_swap_of_index_eq`), which gives four cases.

- `c = a, d = b` contradicts `h1`.
- `c = a, d = swap b` gives `v + v = w a + w a`, so `v = w a`. Halving is pointwise `omega`.
- `c = swap a, d = b` gives `v = w b` in the same way.
- `c = swap a, d = swap b` makes the total sum zero, which contradicts `h2`.

`signedRoot_half_sum` applies `index_eq_or_of_add_self` twice, once for `a` and once for `b`,
using `hv` with `a` and `b` exchanged. Since `index a ≠ index b`, the indices of `c` and `d`
are those of `a` and `b` in some order. Then it calls the previous lemma, exchanging `c` and
`d` if needed.

**Images of weights.** In `exists_map_weightCoord_eq`, pick `a ≠ index x` (`exists_ne`) and
let `y = inl a`. Then `w x - w (swap y)` and `w x - w y` are roots whose sum is `2 w(x)`. By
`hroot` their images are roots `w p + w (swap q)` and `w p' + w (swap q')` (rewritten with
`weightCoord_sub_eq_add`), with `index p ≠ index (swap q)`. Their sum is `2 M(w x)`. Apply
`signedRoot_half_sum` to these two images.

- The images differ. If they were equal, injectivity of `M` would give `w (swap y) = w y`,
  which contradicts `swap_ne_self` and `weightCoord_injective`.
- Their sum is nonzero. It is `M (w x + w x)`, and `w x + w x ≠ 0`.

**Permutation.** In `exists_perm_map_weightCoord`, `choose` gives `f` with `M (w x) = w (f x)`.
The map `f` is injective because `M` and `w` are. Since `l ⊕ l` is finite, `f` is a bijection
(`Equiv.ofBijective`). It commutes with `swap` because `M (w (swap x)) = M (-w x) = -w (f x)
= w (swap (f x))`, and `w` is injective.

## Provenance

This is an internal, elementary lemma, and the parity argument above is ours. In coordinates,
it says that an injective additive endomorphism of `ℤ^l` preserving the roots of type `D_l`
permutes the vectors `±e_a`. This is a well-known fact about the root system `D_l`. No
literature source is cited, and only the Lean statements above are claimed.
