# Separating two Laurent monomials on a nonzero principal open

Worker 194 prepared these internal helpers as support for Task 5365, the generic nonzero
same-Levi intertwiner. They supply the polynomial-clearing step: a finite family of
pointwise inequalities between unramified character values holds on one nonzero
principal open in the published finite coordinates. Products of the polynomials below
give one principal open for a finite family.

## Torus form

`exists_ne_zero_complexTorusPrincipalOpen_monomial_ne` works over a finite index type
`Ix`. Distinct integer exponent vectors `α ≠ β` and any complex scalar `c` give a
nonzero polynomial `p` such that every `z : Ix → ℂˣ` in `complexTorusPrincipalOpen p`
satisfies `∏ z_i^{α_i} ≠ c · ∏ z_i^{β_i}`.

The proof chooses the shift `m_i = |α_i| + |β_i|`, which makes `α + m` and `β + m`
nonnegative, and takes `p = X^{α+m} − C c · X^{β+m}`. The private helper
`shiftedDegree` packages `α + m` as a monomial degree. The private helper
`eval_monomial_shiftedDegree` evaluates the monomial of that degree as the Laurent
monomial times `∏ z_i^{m_i}`. The two shifted degrees differ because `α ≠ β`, so the
coefficient of `X^{α+m}` in `p` is `1` and `p ≠ 0`. If the inequality failed at `z`,
then `p(z) = (∏ z^α − c ∏ z^β) ∏ z^m = 0`, so `z` would not be in the principal open.

## Rational-character form

`exists_ne_zero_rationalUnramifiedPrincipalOpen_apply_ne` works over an actual
nonarchimedean local field `F`, for a connected reductive group scheme `G`. Take
rational points `x, y` with distinct images
`rationalValuationImageProjection G x ≠ rationalValuationImageProjection G y` in the
valuation lattice, and any `c : ℂ`. Then there is a nonzero polynomial in the published
coordinates `Fin (rationalImageRank G)` such that every unramified character `χ` in
`rationalUnramifiedPrincipalOpen G hG p` satisfies `χ(x) ≠ c · χ(y)`.

The proof expresses the two lattice images in the published basis
`rationalReductiveValuationBasis G hG`. The coordinate vectors differ, because `repr`
and `Additive.ofMul` are injective. The torus form is then applied to those vectors.
`rationalCanonicalUnramifiedCharacterCoordinates_symm_apply` rewrites `χ(x)` and `χ(y)`
as the corresponding Laurent monomials in the coordinates of `χ`.

The provenance is internal. The argument is elementary polynomial algebra in the
published coordinates. It makes no literature claim.
