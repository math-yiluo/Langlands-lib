# Schur lemmas for block-diagonal representations

Complex representations of a group `J` are used here. Each lemma states below whether
it needs finite dimensionality.

- `end_scalar`: every endomorphism of an irreducible representation on a
  finite-dimensional complex space (`[FiniteDimensional ℂ V]`) is a scalar, by Schur's
  lemma over the algebraically closed field `ℂ`.
- `nonempty_equiv_of_ne_zero`: a nonzero intertwiner between irreducible
  representations is an equivalence, since its kernel and image are subrepresentations.
  No finiteness is needed.
- `isIrreducible_comp_surjective`: precomposing with a surjective homomorphism
  preserves irreducibility, because both representations have the same
  subrepresentations.

For a family of representations `ρ k` on the same space `V`, indexed by a finite type,
`blockRep ρ` acts diagonally on `I → V`. `entry T hT j k` is the `(j, k)` matrix entry
of an equivariant endomorphism `T`, as an intertwiner from `ρ k` to `ρ j`.

- `blockRep_endo_diag`: suppose `V` is finite-dimensional over `ℂ`, all blocks are
  irreducible and there is no nonzero intertwiner between distinct blocks. Then every
  equivariant endomorphism is a diagonal scalar matrix: off-diagonal entries vanish,
  and diagonal entries are scalars by `end_scalar`.
- `exists_block_equiv`: let `P : (I → V) → Y` be a nonzero equivariant map to an
  irreducible representation `y`, with all blocks irreducible. No finiteness of `V` or
  `Y` is needed. Then some block is
  equivalent to `y`. The restriction of `P` to the coordinate `k` is nonzero for some
  `k`, and `nonempty_equiv_of_ne_zero` applies to that restriction.

These are standard Clifford-theory lemmas, stated for the internal use in the proof
of Henniart (1988), Proposition 2.2.
