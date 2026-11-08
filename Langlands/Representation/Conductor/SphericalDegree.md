# Normalized determinant and actual Iwasawa degree

This internal unit identifies the previously constructed Iwasawa degree with
the normalized determinant strata used in corank-one integrals. The field
`F : Type uF` is arbitrary: it has a field structure and a valuative relation;
no topology is needed.
Neither the nonarchimedean local-field hypothesis nor any representation is
needed for these comparisons.

## The actual quotient determinant

`quotientDeterminantNorm abv` is the function on
`N_(n+1)(F) \ GL_(n+1)(F)` induced by `g ↦ abv(det g)`, where `abv` is a
real-valued absolute value. Upper-unipotent determinants are one, so the
function is independent of the representative.
`quotientDeterminantNorm_mk` gives its value at an actual representative.

Fix a uniformizing unit `ϖ` and its proof `hϖ`, and assume `abv` is one on
elements whose valuation is one. `abv_det_eq_zpow_exponent` proves

`abv(det g) = abv(ϖ) ^ (∑ i, exponent hϖ g i)`.

The proof uses the existing Iwasawa decomposition of `g` as upper unipotent,
diagonal powers of `ϖ`, and an integral matrix. The first determinant is one;
the integral factor has valuation one and hence absolute value one. The
diagonal determinant is the product of its diagonal entries. Multiplicativity
of the absolute value and the finite-product law for integral powers give the
asserted sum.

## The normalized sign and spectral power

For any natural number `q` with `abv(ϖ) = (q : ℝ)⁻¹`,
`quotientDeterminantNorm_eq_qpow` descends the comparison to the quotient:

`quotientDeterminantNorm abv t = (q : ℝ) ^ (-sphericalQuotientDegree hϖ t)`.

Thus a degree `d` point has determinant norm `q^(-d)`. For `q > 1`,
`sphericalQuotientDegree_eq_iff_norm` proves the converse as well, using strict
monotonicity of integral powers of a real base greater than one. This records
the sign explicitly.

For `q > 0`, `determinantWeight_eq_degree_power` proves, for every complex
parameter `s`,

`determinantWeight abv g s = ((q : ℂ) ^ (-s)) ^ (∑ i, exponent hϖ g i)`.

The outer power on the right is an integer power; `q ^ (-s)` is the existing
complex power. After the determinant comparison and conversion from real
integer powers to complex integer powers, Mathlib's complex power identities
apply. The positive real base `q` has complex argument zero, which supplies
the branch bounds required to move the integer power through the complex
power. The remaining equality is the identity
`(-d) * s = d * (-s)`.

## Scope and provenance

These are internal deductions from the actual Iwasawa decomposition,
upper-unipotent and integral determinant lemmas, and Mathlib's absolute-value
and real/complex power laws. The unit defines an actual descended function
and proves its comparisons; it introduces no new factor or normalization
premise beyond the explicit absolute-value hypotheses above. It proves no
compact support, convergence, essential identity or conductor conclusion.
