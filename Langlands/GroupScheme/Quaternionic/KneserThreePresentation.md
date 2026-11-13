# Quaternion-type rings presented over a commutative ring with involution

Module `Langlands.GroupScheme.Quaternionic.KneserThreePresentation`, namespace
`Langlands.GroupScheme.KneserThree`. Internal algebra, with no characteristic assumption.

## The structure

`Presentation A B`, for a commutative ring `A` and a ring `B`, consists of

* `c : SU3Root.RingInvolution A` (written `a ↦ ā`), a ring homomorphism `ι : A →+* B`, an element
  `j : B` and `δ : A` with `δ̄ = δ`;
* the relations `j * ι a = ι ā * j` (`j_mul`) and `j * j = ι δ` (`j_mul_self`);
* additive maps `fst snd : B →+ A` with `ι (fst b) + j * ι (snd b) = b` (`decompose`) and
  `fst (ι a + j ι a') = a`, `snd (ι a + j ι a') = a'` (`fst_mk`, `snd_mk`).

So every `b` is uniquely `ι a + j ι a'`. Example: a quaternion algebra `D = L ⊕ jL` over a
quadratic subfield `L` with `jℓ = ℓ̄j`, base-changed to a commutative coefficient ring.

## Definitions and results

* `elem a a' = ι a + j * ι a'`; `fst_elem`, `snd_elem`, `elem_fst_snd`, and `ext` (equality from
  equal components).
* `elem_mul`: `elem a a' * elem e e' = elem (a e + δ ā' e') (ā e' + a' e)`; hence `fst_mul` and
  `snd_mul`. Also `fst/snd` of `1`, `ι a` and `j`.
* `rep b = [[fst b, δ · conj (snd b)], [snd b, conj (fst b)]]`, the matrix of left multiplication
  by `b` on `B = A ⊕ jA` in the right `A`-basis `(1, j)`. `rep_mul`, `rep_add`, `rep_zero`,
  `rep_one`, `rep_sum`, `rep_injective`.
* `bar b = elem (conj (fst b)) (-(snd b))`, the conjugation `ι a + j ι a' ↦ ι ā - j ι a'`;
  `symplectic = [[0, 1], [-1, 0]]` and `rep_bar_mul_symplectic`:
  `rep (bar b) * symplectic = symplectic * (rep b)ᵀ` (the adjugate identity).
* `block X` for a square matrix `X` over `B` indexed by `n` is the matrix over `A` indexed by
  `n × Fin 2` whose `(i, a), (k, b)` entry is `rep (X i k) a b`. `block_mul`, `block_one`,
  `block_injective`.
* `conjTranspose X` is `(X^*)_{ik} = bar (X k i)`; `blockSymplectic` is the block diagonal matrix
  with blocks `symplectic`. `block_conjTranspose_mul`:
  `block (conjTranspose X) * blockSymplectic = blockSymplectic * (block X)ᵀ`, and
  `blockSymplectic_mul_self`: `blockSymplectic * blockSymplectic = -1`.

The proofs expand the `2 × 2` matrices and use `ring`, after rewriting products with
`elem_mul`.
