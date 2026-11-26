# Block upper unipotent matrices from their entry pattern

Lean module: `Langlands.Group.GL.BlockUnipotentPattern`, namespace `Langlands.GeneralLinear`.

Over a commutative ring `R` and for `h : a + b = n`:

- `blockCut h : Fin a ⊕ Fin b ≃ Fin n` is the consecutive numbering used by the Library's
  `blockUnipotent h X = [[1, X], [0, 1]]`; `blockCut_inl_val` and `blockCut_inr_val` give the
  positions `i` and `a + j`.
- `blockUnipotent_apply_blockCut` computes the entries of `blockUnipotent h X` in these
  coordinates as those of `Matrix.fromBlocks 1 X 0 1`.
- `upperRightBlock h A` is the upper right `a × b` block of an `n × n` matrix.
- `eq_blockUnipotent_of_pattern`: an invertible matrix `g` whose entries `g i j` with `j < a`
  or `a ≤ i` are those of the identity matrix equals
  `blockUnipotent h (upperRightBlock h g)`. The proof compares the four blocks entrywise.

Provenance: elementary matrix algebra, internal to the Library.
