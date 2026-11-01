# Tensor signs for `ComplexShape.up ℕ`

Lean module: `Langlands.Cohomology.ModuleComplex.TensorSignsUpNat`.

## Content

Mathlib (pinned commit `5ed29652`) provides `ComplexShape.TensorSigns` instances
for `ComplexShape.down ℕ` and `ComplexShape.up ℤ`
(`Mathlib/Algebra/Homology/ComplexShapeSigns.lean`), but none for
`ComplexShape.up ℕ`, the shape of the Čech cochain complexes used in the
Library. Without it there is no
`TotalComplexShape (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)`
instance, so `HomologicalComplex.mapBifunctor K₁ K₂ F (ComplexShape.up ℕ)`
(the total complex of the external tensor product of two `ℕ`-indexed cochain
complexes) cannot be formed.

- `Langlands.Cohomology.ModuleComplex.tensorSignsUpNat` : the instance
  `ComplexShape.TensorSigns (ComplexShape.up ℕ)` with sign homomorphism
  `ε' p = (-1 : ℤˣ) ^ p`. The fields are: `rel_add` and `add_rel` (if
  `p + 1 = q` then `(p + r) + 1 = q + r` and `(r + p) + 1 = r + q`) and
  `ε'_succ` (`(-1) ^ (p + 1) = -((-1) ^ p)`).
- `Langlands.Cohomology.ModuleComplex.ε_up_ℕ` (simp, `rfl`):
  `(ComplexShape.up ℕ).ε n = (-1 : ℤˣ) ^ n`.

Through Mathlib's generic instance `TotalComplexShape c c c` for a shape with
tensor signs, the total-complex differential on the `(p, q)` summand is
`d₁ + (-1)^p d₂` (the first factor's differential with sign `1`, the second
with sign `ε p`), the usual Koszul sign convention.

## Provenance

This is a direct copy of Mathlib's `TensorSigns (ComplexShape.down ℕ)` instance
(same sign homomorphism, same proof of the sign identity), with the relation
reversed from `q + 1 = p` to `p + 1 = q`. It is a sign convention, not a
mathematical result.
