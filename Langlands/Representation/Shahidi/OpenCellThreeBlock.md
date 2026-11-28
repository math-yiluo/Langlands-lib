# Lifts with inner Jacquet functions

Module `Langlands.Representation.Shahidi.OpenCellThreeBlock`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `liftFunction_unipotent_mul_torus`: for a Levi-invariant `Φ`, the lift at `u ϖ^ν` is `Φ` at the
  diagonal blocks of `u ϖ^ν`.
- `determinantNorm_blockWeyl_mul_intertwiningUnipotent(_real)`: `|det(w u'(z))| = 1`;
  `twoBlockModulus_mul_first/second`: the two-block modulus is unchanged by left multiplication
  of one block by an element `h` with `|det h| = 1`.
- `exists_eq_upper_mul_blockSum_mul`: every element is `u(X) diag(m₁, m₂) k` with `k` integral.
- `liftFunction_degreePiece_prodΦ_jacquet_first`: let `Φ₁` be a Levi-invariant Levi function on
  a first block of type `(r₁ + 1, t₁ + 1)` and `Ψ₂` right invariant under `GL_(t+1)(𝒪)`. Then
  the lift of the degree-`D` piece of `prodΦ s J[Φ₁] Ψ₂` is, at every `g`, the (Bochner) integral
  over the inner variable,
  `F(g) = ∫ conj ψ(z_(t₁,0)) F'(diag(w' u'(z), 1) g) dz`, where `F'` is the lift of the degree-`D`
  piece of `prodΦ s F₁ Ψ₂` and `F₁` the lift of `Φ₁`;
  `liftFunction_degreePiece_prodΦ_jacquet_second`: the analogue in the second block (with `Ψ₁`
  right invariant and `Φ₂` Levi-invariant),
  `F(g) = ∫ conj ψ(Y_(t₁,0)) F'(diag(1, w'' u''(Y)) g) dY`. No integrability hypothesis is
  needed: both sides are the same Bochner integral after the transformation law of lifts.

## Provenance

Derived from the transformation law of lifts: `diag(h, 1) u(X) diag(m₁, m₂) =
u(h X) diag(h m₁, m₂)` and `|det h| = 1`.
