# Quotients compared through endomorphisms congruent to the identity

This internal module compares the quotients `Q / (I + 𝔫 ^ n)` and
`Q / (I' + 𝔫 ^ n)` of a ring through a ring endomorphism that is congruent to the
identity to first order. It replaces the length comparison in the proof of Stacks
Project Lemma 98.12.7 (Tag 07XH, `artin.pdf`, printed pp. 20–21). There, a surjection
`R → A^∧` is an isomorphism because both sides have the same associated graded
dimensions. Here no lengths or associated graded rings are used. The provenance is
derived from that step. The formulation is internal.

Throughout, `Q : Type u` is a commutative ring and `𝔫 : Ideal Q`.

`sub_mem_pow_succ_of_forall_sub_mem_sq` applies to a ring endomorphism
`Φ : Q →+* Q` with `Φ x - x ∈ 𝔫 ^ 2` for all `x`. For every `k` and every
`x ∈ 𝔫 ^ k` it proves `Φ x - x ∈ 𝔫 ^ (k + 1)`. The proof uses induction on `k` and
the identity
`Φ (a * b) - a * b = Φ a * (Φ b - b) + (Φ a - a) * b`.

From now on `Φ` satisfies the conclusion of that lemma for all `k`: `Φ` is
near-identity.

- `exists_sub_map_mem_pow`: for every `k` and `y`, some `x` has
  `y - Φ x ∈ 𝔫 ^ k`. Inductively, if `e = y - Φ x ∈ 𝔫 ^ k`, then
  `y - Φ (x + e) = -(Φ e - e) ∈ 𝔫 ^ (k + 1)`.
- `mem_pow_of_map_mem_pow`: `Φ y ∈ 𝔫 ^ n` implies `y ∈ 𝔫 ^ n`. Inductively, if
  `y ∈ 𝔫 ^ k` with `k < n`, then `y = Φ y - (Φ y - y)` lies in `𝔫 ^ (k + 1)`.

`map_mem_sup_iff` fixes ideals `I`, `I'` and `n : ℕ` and assumes:

- `Φ x ∈ I' ⊔ 𝔫 ^ n` for every `x ∈ I`;
- `I' ⊓ 𝔫 ^ d ≤ I ⊔ 𝔫 ^ (d + 1)` for every `d < n`.

Then for every `x`, `Φ x ∈ I' ⊔ 𝔫 ^ n` if and only if `x ∈ I ⊔ 𝔫 ^ n`.

The key step shows, for `d ≤ n`, that every `z ∈ I'` has `i ∈ I` with
`z - Φ i ∈ (I' ⊔ 𝔫 ^ n) ⊓ 𝔫 ^ d`. If `z - Φ i = a + e` with `a ∈ I'` and
`e ∈ 𝔫 ^ n`, then `a ∈ I' ⊓ 𝔫 ^ d`. The second hypothesis writes `a = j + f` with
`j ∈ I ⊓ 𝔫 ^ d` and `f ∈ 𝔫 ^ (d + 1)`. Replacing `i` by `i + j` gives
`z - Φ (i + j) = -(Φ j - j) + f + e ∈ 𝔫 ^ (d + 1)`. At `d = n`, if
`Φ x = a + e` with `a ∈ I'`, choose `i` for `a`. Then `Φ (x - i) ∈ 𝔫 ^ n`, so
`x - i ∈ 𝔫 ^ n`. The converse uses the first hypothesis and `Φ e ∈ 𝔫 ^ n` for
`e ∈ 𝔫 ^ n`.

`ker_comp_eq_and_surjective` packages this result. Let `q' : Q →+* B` have kernel
`I' ⊔ 𝔫 ^ n` and be surjective. Then `q'.comp Φ` has kernel `I ⊔ 𝔫 ^ n` and is
surjective. Surjectivity uses `exists_sub_map_mem_pow` at stage `n`.
