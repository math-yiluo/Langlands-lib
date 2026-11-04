# Weighted leading terms over a discrete valuation ring

This module is an internal helper for the proof of Conrad--Gabber--Prasad,
*Pseudo-reductive groups* (2nd ed., 2015), Proposition C.1.6. It replaces the
root-group valuation step of that proof by an elementary statement about
weighted-homogeneous polynomials. The statement and its proof are derived here;
they are not quoted from the source.

Throughout, `A` is a discrete valuation ring (a domain with
`IsDiscreteValuationRing A`), `FractionRing A` is its fraction field and
`ResidueField A` its residue field.

## `exists_eq_mul_zpow`

For an irreducible element `ϖ` of `A` and any `x` in the fraction field, there
are `u : A` and `z : ℤ` such that `u = 0` or `u` is a unit, and
`x = u * ϖ ^ z` (with `u` and `ϖ` mapped to the fraction field). For `x = 0` take
`u = 0`, `z = 0`. Otherwise write `x = a / b` with `a, b ∈ A` nonzero, factor
`a = u ϖ^n` and `b = v ϖ^m` with units `u, v`, and take the unit `u v⁻¹` and the
exponent `n - m`.

## `prod_zpow_pow`

In a field, for `π ≠ 0`, a finite product `∏ (π ^ z i) ^ n i` equals
`π ^ (∑ n i * z i)`. This is proved by induction on the finite set.

## `exists_ne_zero_forall_aeval_eq_zero`

Let `ι` be a finite index type, `w : ι → ℕ` positive weights, and `S` a set of
polynomials in `MvPolynomial ι A` each of which is weighted homogeneous (for `w`)
of some positive degree `d`. Let `ξ : ι → FractionRing A` be a point such that
every `f ∈ S` takes a value `f(ξ)` in (the image of) `A`, while some coordinate
`ξ i` is not in `A`. Then there is a nonzero point `a : ι → ResidueField A` such
that `f(a) = 0` for every `f ∈ S` (evaluating the residue images of the
coefficients of `f`).

Proof as implemented. Fix an irreducible `ϖ` and write `ξ i = u i * ϖ ^ z i` as
above. Let `T` be the set of indices with `u i ≠ 0`, and `r i = -z i / w i ∈ ℚ`.
The non-integral coordinate `i0` has `u i0 ≠ 0` and `z i0 < 0`, so `T` is nonempty
and `M = max_{i ∈ T} r i` is positive. Set
`a i = residue (u i)` when `u i ≠ 0` and `r i = M`, and `a i = 0` otherwise; the
index attaining the maximum shows `a ≠ 0`, since `u` is then a unit.

For `f ∈ S` of degree `d`, let `N = ⌈M d⌉ > 0`. For a monomial `ξ^α` with all
variables in `T`, its "pole order" `s α = ∑ α i * (-z i)` satisfies
`s α ≤ M * (weight of α) = M d ≤ N`, because `-z i ≤ M w i` on `T`. Hence
`g = ∑_α coeff_α(f) * (∏ u i ^ α i) * ϖ ^ (N - s α)` is an element of `A` (monomials
involving a variable outside `T` contribute `0`), and `g = ϖ^N f(ξ)` in the fraction
field. As `f(ξ) = b ∈ A`, `g = ϖ^N b`, so the residue of `g` is `0`.

Finally the residue of `g` equals `f(a)` term by term. If every variable of `α`
is tight (`u i ≠ 0` and `r i = M`), then `s α = M d` is an integer, so
`N = s α`, the power of `ϖ` is `ϖ^0`, and the term reduces to
`coeff_α(f) * ∏ a i ^ α i`. Otherwise some variable of `α` has `a i = 0`, so the
term of `f(a)` vanishes; on the other side, either some `u j = 0` occurs in `α`, or
some variable is strictly below the maximum, which makes `s α < M d ≤ N`, so a
positive power of `ϖ` appears and the residue is `0`. Hence `f(a) = 0`.

## Intended role in C.1.6

This module proves only the algebraic statements above. The intended use in the
C.1.6 argument: the coordinates of a `K`-point of an opposite open cell are `ξ`,
the cell's coordinate ring is positively graded by a cocharacter, and the
equations of a kernel are weighted homogeneous of positive degree. If the image
of the point extends over `A` but `ξ` is not integral, the lemma gives a nonzero
residue-field point of that kernel.
