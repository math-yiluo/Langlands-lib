# Uniqueness up to unramified twist

`twist_equiv_of_inertia_ne_zero` concerns two irreducible finite-dimensional
representations of a split group with a nonzero intertwiner between their inertia
restrictions. They differ by an unramified twist: `exists_twisted_intertwiner` gives a
nonzero intertwiner from a twist, and `nonempty_equiv_of_ne_zero` makes it an
equivalence.

For a stage `S` of degree `m + 1` and a representation `τ` of `H` on a complex vector
space `V` (no finiteness is needed for these three):

- `comp_inertia_eq_block`: the restriction of `τ` to stage inertia is the first block
  composed with `ιJ`.
- `block_eq_comp`: the `k`th block is the first block composed with `cj k`.
- `proj0`: the projection to coordinate `0` is an inertia intertwiner from the
  coinduction to the first block. It is nonzero when `V` is nontrivial (`proj0_ne_zero`).

`twist_equiv_coind_of_occurs` assumes that `τ` acts on a nonzero finite-dimensional
complex space `V` (`[Nontrivial V]`, `[FiniteDimensional ℂ V]`), and that the blocks of
`τ` are irreducible and pairwise unrelated. Let `σ'` be an irreducible representation
of `G` on a finite-dimensional complex space `V'` (`[FiniteDimensional ℂ V']`), with a
nonzero inertia intertwiner `P` from `σ'` to the first block. Then some unramified
twist of `σ'` is equivalent to `S.coind τ`. Both finiteness hypotheses are used: that
of `V` makes the coinduction irreducible (`coind_isIrreducible`), and `V'` and `V`
must be finite-dimensional for `exists_twisted_intertwiner`. The proof has four
steps:

1. Restricted along `ι`, `P` is a nonzero inertia intertwiner from `σ' ∘ ι` to `τ`.
2. `exists_twisted_intertwiner` for `E` gives `z` and a nonzero intertwiner `F` from the
   `z`-twist of `σ' ∘ ι` to `τ`.
3. Choose `u` with `u^{m+1} = z`, which exists because `ℂ` is algebraically closed.
   By `unramifiedCharacter_ι`, `F` is a stage intertwiner from the `u`-twist of `σ'`.
4. Frobenius reciprocity (`recip_intertwines`) gives a nonzero intertwiner into the
   irreducible coinduction, hence an equivalence.

This is the uniqueness half of the classification in Henniart (1988),
Proposition 2.2, as an internal lemma.
