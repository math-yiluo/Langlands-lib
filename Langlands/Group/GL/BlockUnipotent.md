# Upper block-unipotent matrices

Author: Worker 35. These declarations were separated from the constant-term
module for use by both automorphic and local representation theory.
Their definitions and proofs are unchanged.

## Block unipotent matrices (`Langlands.GeneralLinear`)

`R` is any commutative ring and `a b n : ℕ`.

- `sumBlockUnipotent X`, for `X : Matrix (Fin a) (Fin b) R`, is the invertible
  block matrix `[[1, X], [0, 1]]` (Mathlib's `Matrix.fromBlocks 1 X 0 1`) indexed by
  `Fin a ⊕ Fin b`. Its stored inverse is `[[1, -X], [0, 1]]`, and both inverse laws
  are proved.
- `blockUnipotent h X`, for `h : a + b = n`, is the image of `sumBlockUnipotent X`
  in `GeneralLinear n R` under the Library's `reindex` along the standard
  consecutive numbering `finSumFinEquiv.trans (finCongr h) : Fin a ⊕ Fin b ≃ Fin n`.
  Thus the first `a` indices form the first block. `blockUnipotent_val` records its
  matrix.
- Proved properties: `blockUnipotent_zero` (`u(0) = 1`), `blockUnipotent_add`
  (`u(X + Y) = u(X) u(Y)`), `map_blockUnipotent` (compatibility with a ring
  homomorphism applied entrywise) and `continuous_blockUnipotent` (continuity
  for a topological ring, into the units topology).

So `X ↦ blockUnipotent h X` is an injective group homomorphism from the additive
group of `a × b` matrices onto the unipotent radical `N_{a,b}` of the standard upper
block parabolic `P_{a,b}` of `GL_n`, with Levi blocks `GL_a × GL_b`. The image
statement is the usual description of `N_{a,b}`; only the homomorphism and
continuity are formalized.

