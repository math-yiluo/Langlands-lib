# The split Cayley datum

Author: Worker 161.

This module constructs `CayleyDatum.split K`, an actual Cayley datum over
every field `K`, in every characteristic including two. The multiplication
is Zorn's vector-matrix product. An element of `R⁸`, for any commutative
ring `R`, has coordinates `(a, u₁, u₂, u₃, v₁, v₂, v₃, b)` and is read
as the vector matrix with scalars `a`, `b` on the diagonal and vectors
`u`, `v` off the diagonal. With the dot product `·` and the cross product
`×` on `R³`, the product is

`(a, u, v, b)(a', u', v', b') =
  (a a' + u·v', a u' + b' u - v × v', a' v + b v' + u × u', b b' + v·u')`.

The code calls this map `SplitCayley.mulFun R`. `SplitCayley.mul R` packages
it as an `R`-bilinear map; each bilinearity identity is checked coordinate
by coordinate with `ring`. The identity vector `SplitCayley.unit R` is
`(1, 0, 0, 1)`. The norm `SplitCayley.norm R` is the quadratic form
`a b - u·v`, the diagonal of the bilinear form
`SplitCayley.normBilin R (x, y) = x₀ y₇ - (x₁ y₄ + x₂ y₅ + x₃ y₆)`.
The multiplication is not associative, and the module gives it no
`Algebra` structure.

Proved identities, over every commutative ring `R`:

- `unit_mul` and `mul_unit`: `(1, 0, 0, 1)` is a two-sided identity. They
  are checked coordinatewise by `simp`.
- `norm_unit`: the identity has norm one.
- `norm_mul`: the norm is multiplicative. This is a polynomial identity in
  the sixteen coordinates, proved by `ring` after expanding both sides.
- `polar_norm`: the polar form of the norm is
  `x₀ y₇ + x₇ y₀ - Σᵢ (xᵢ y_{i+3} + x_{i+3} yᵢ)` for `i = 1, 2, 3`. The
  proof uses Mathlib's `LinearMap.BilinMap.polar_toQuadraticMap`.
- `polar_nondegenerate`: if the polar form of `x` vanishes against every
  vector, then `x = 0`. The polar form pairs coordinates `0 ↔ 7` and
  `i ↔ i + 3` with unit coefficients ±1. Testing against each standard
  basis vector therefore recovers each coordinate of `x`. No division by
  two occurs, so this holds in characteristic two.
- `map_mulFun`: applying a ring homomorphism coordinatewise commutes with
  the Zorn product, since its coordinates are integer polynomials.
- `bilinear_apply_eq_sum`: every bilinear map `B` on `A⁸` satisfies
  `B x y i = Σ_j Σ_k B(e_j, e_k)_i x_j y_k`. Both vectors are expanded in
  the standard basis.

`CayleyDatum.split K` assembles these over a field `K`. The datum's
`polar_nondegenerate` field uses `polarBilin`, which agrees definitionally
with `polar`. Two compatibility results with the Library's coefficient
extension follow:

- `split_multiplicationOver`: for every ring homomorphism `φ : K →+* A`,
  `(split K).multiplicationOver φ` is exactly the Zorn product over `A`.
  `multiplicationOver` is defined by the structure constants
  `(split K).structureConstant i j k`. These are the coordinates of Zorn
  products of standard basis vectors over `K` (`split_structureConstant`).
  `map_mulFun` sends them to the same products over `A`. Then
  `bilinear_apply_eq_sum` for `SplitCayley.mul A` closes the
  comparison.
- `split_unitOver`: `(split K).unitOver φ = (1, 0, 0, 1)` over `A`.

These two results let later modules compute the automorphism equations of
the split datum over any test algebra, including nonreduced ones, as
equations for the Zorn product over that algebra.

## Source

Knus, Merkurjev, Rost and Tignol, *The Book of Involutions* (1998),
registered as `knus-merkurjev-rost-tignol-1998-book-of-involutions`,
defines the split Cayley algebra in Section 33.C, printed p.462 / PDF
p.485, as the Cayley–Dickson double `CD(M₂(F), -1)`, with hyperbolic
eight-dimensional norm. The vector-matrix coordinates here are a derived
model, attributed to Zorn, and are not used in the cited pages. They define
the same algebra up to isomorphism, by the following argument from the
source. The proved identities make `CayleyDatum.split K` an
eight-dimensional unital composition algebra. Theorem 33.17, printed
pp.459–460 / PDF pp.482–483, makes it a Cayley algebra. Its norm is
isotropic, since `(1, 0, 0, 0)` has norm zero. Theorem 33.19 and
Proposition 33.23, printed pp.460–461 / PDF pp.483–484, then identify it
with the source's split Cayley algebra. This module proves neither that
identification nor anything about its automorphism group; it only
constructs the datum and checks the axioms of `CayleyDatum`.
