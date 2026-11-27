# The special unitary Hasse principle in rank one

Module: `Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisRankOne`.

For a `1 × 1` Gram matrix `H = (h)`, `SU(h)` is the norm-one torus of the quadratic
extension `F(h)` (Kneser, *Lectures on Galois Cohomology of Classical Groups* (TIFR Lectures on Mathematics 47, 1969), §3.1 Example 4), and its Hasse principle is the Hasse norm theorem for
quadratic extensions (Kneser, *Lectures on Galois Cohomology of Classical Groups* (TIFR Lectures on Mathematics 47, 1969), §3.3, Theorem 6(a), printed p. 41; used in §5.11, printed p. 102). The module proves it in the form
`suHasse_one : SUHasse σ hdim hsym 1`.

- `matrix_fin_one_eq_diagonal`, `fin_one_mul_apply`, `matrixReducedNorm_fin_one`: a `1 × 1`
  matrix is the scalar matrix of its entry, and its reduced norm is that of the entry.
- `matrixReducedNorm_coeffMap`, `matrixReducedNorm_units_inv`: naturality and inverses.
- `GramDescent.exists_isometry_norm_of_coboundary`: the local isometry `t` of
  `GramDescent.exists_isometry_of_coboundary` also has reduced norm `ν` when the Hilbert 90
  primitive `p` has reduced norm `ν ∈ F`, since `t` descends `b⁻¹ p` with `b` of reduced norm
  one.
- `hasIntertwinerOfNorm_of_isometry`: from `t (g) t* = (h)` with `Nrd t = ν`, the element
  `x = t⁻¹` satisfies `ν⁻¹ x h = g x` and `Nrd x = ν⁻¹` (using `x x* = Nrd x` for the
  canonical conjugation, `quaternionConjugation_norm_baseChange`).

Proof of `suHasse_one`: write `c s = p * s(p)⁻¹` with descended Gram matrix `(g)`. Since every
`c s` has reduced norm one, `Nrd p` is Galois fixed, equal to `ν ∈ F`, `ν ≠ 0`. At every
completion the local coboundary data give an intertwiner of reduced norm `ν⁻¹`
(`HasIntertwinerOfNorm`), so `exists_intertwiner_of_local` gives `y ∈ D` with
`ν⁻¹ y h = g y` and `Nrd y = ν⁻¹`. Then `y h y* = g` and `a = p (1 ⊗ y)` lies in
`suGroup τ H L` with `c s = a * s(a)⁻¹`.
