# Values of lifted functions on the open cell of the `(1, n)` parabolic

Module `Langlands.Representation.Shahidi.OpenCellBaseLift`, namespace
`Langlands.Shahidi.OpenCell.Base`.

For a function lifted from the Levi of the `(1, t+2)` parabolic and a column `y = (y', c)`:

- `liftFunction_lower_of_inv_mem`: let `c ≠ 0` with `c⁻¹` integral, let `Φ` (on
  `GL_1 × GL_(t+2)`) and `Φ'` (on `GL_1 × GL_(t+1)`) be Levi-invariant, and let `χ ∈ ℂ` satisfy
  `Φ(c⁻¹ m₁, u(y'/c) diag(1, c) diag(m₂, 1)) = χ Φ'(m₁, m₂)` for all `m₁`, `m₂` (with `u(·)` the
  upper unipotent matrix of `GL_((t+1)+1)`). Then `F(lower(y)) = χ F'(lower(y'/c))` for the lifts
  `F`, `F'` (via the factorization `lower_eq_p0GL_mul` of
  `Langlands.Representation.Shahidi.OpenCellBaseMatrix`, whose last factor is integral when
  `c⁻¹` is).
- `liftFunction_lower_of_mem`: for a Levi-invariant `Φ` and integral `c`, `F(lower(y))` is the lift
  of the restricted Levi function `(m₁, m₂) ↦ Φ(m₁, diag(m₂, 1))` (Levi-invariant by
  `isLeviInvariant_restrict`) at `lower(y')` (via `lower_eq_embed_mul`).

The remaining lemmas check integrality of the auxiliary matrices and compute `liftFirst`,
`liftSecond` of the explicit parabolic factors.

## Provenance

Derived from the transformation law of lifts (`Langlands.Representation.Shahidi.OpenCellLift`).
