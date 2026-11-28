# Functions lifted from the Levi of the upper two-block parabolic

Module `Langlands.Representation.Shahidi.OpenCellLift`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `exists_liftShape_parabolic_mul`: every `x ∈ GL_((r+1)+(t+1))(K)` is `g k` with `g` in the
  upper two-block parabolic and `k` integral (Iwasawa decomposition).
- `liftFirst`, `liftSecond`: the diagonal blocks of a parabolic element; they are
  homomorphisms; `exists_eq_upper_mul_blockSum`: `g = u(X) diag(g₁, g₂)`.
- `IsLeviInvariant Φ`: right invariance of a Levi function `Φ(m₁, m₂)` under integral Levi
  elements.
- `liftFunction hϖ Φ`: the lift `x ↦ Φ(g₁, g₂)`, evaluated at one chosen decomposition
  `x = g k` (for an arbitrary `Φ` the value depends on that choice).
- For a Levi-invariant `Φ`: `liftFunction_parabolic_mul`: the value at `g k` is `Φ(g₁, g₂)` for
  every such decomposition; `liftFunction_law`: `F(u(X) diag(m₁, m₂) k) = Φ(m₁, m₂)` for every
  `X`, `m₁`, `m₂` and integral `k`; `liftFunction_mul_integral`: right invariance under integral
  matrices; `liftFunction_parabolic_mul_left`: left translation by a parabolic element multiplies
  the Levi arguments by its diagonal blocks; `eq_liftFunction`: a function with this law is the
  lift; `liftFunction_lower`: the value at `lower(Y)` is `Φ(u₁ ϖ^λ, u₂ ϖ^μ)` for some upper
  unipotent `u₁`, `u₂`, where `λ`, `μ` are the two blocks of the Iwasawa exponent of `lower(Y)`.

## Provenance

The lift is the function on `GL_((r+1)+(t+1))(K)` that is left invariant under the unipotent
radical of the parabolic, given by `Φ` on the Levi and right invariant under the integral matrices,
written through the Iwasawa decomposition; for a Levi-invariant `Φ` the independence of the choice
uses that two decompositions differ by an integral parabolic element.
