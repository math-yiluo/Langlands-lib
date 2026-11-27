# Twisted conjugators between parabolic elements over a window

Module `Langlands.BaseChange.TwistedLocalDescent.Rigidity`.

- `normCharpoly_of_mem_saturation`: if `σ^l = 1`, then on the `M(E)`-twisted conjugacy
  saturation of a set `Ω` the norm characteristic polynomials of the blocks take the values they
  take on `Ω` (`normCharpoly_twistedConj`).
- `block_cyclicNorm_parabolic`: the diagonal blocks of the norm of a parabolic element are the
  norms of the blocks of its Levi part.
- `mem_parabolic_of_twistedConj` (**rigidity**): let `σ^l = 1` and `Ω ⊆ M(E)` a set such that
  for all `x, x' ∈ Ω` and distinct blocks `i ≠ i'` the norm characteristic polynomial of the
  block `x'_{i'}` is coprime to that of the block `x_i` (the windows of `exists_windows`). If
  `p, p' ∈ P(E)` have Levi parts in the twisted conjugacy saturation of `Ω` and
  `h p σ(h)⁻¹ = p'` for some `h ∈ GL_n(E)`, then `h ∈ P(E)`.

  The comparison across two points of `Ω` is needed: coprimality at each point separately does
  not suffice. In the ordinary two-block case of `GL_2`, a set containing `diag(a, b)` and
  `diag(b, a)` with `a ≠ b` satisfies it, and the block swap conjugating one to the other is not
  upper triangular.

  Proof: twisted conjugation turns into ordinary conjugation of norms,
  `h N(p) h⁻¹ = N(p')` (`cyclicNorm_twistedConj` with `σ^l = 1`). Both norms are block upper
  triangular with diagonal blocks the norms of the Levi blocks. The Levi parts of `p` and `p'`
  have the norm characteristic polynomials of some `x, x' ∈ Ω`
  (`normCharpoly_of_mem_saturation`), so block `i` of `N(p)` and block `i' ≠ i` of `N(p')` have
  coprime characteristic polynomials. The block intertwiner lemma `isBlockUpper_of_mul_eq` then
  makes `h` block upper triangular.
