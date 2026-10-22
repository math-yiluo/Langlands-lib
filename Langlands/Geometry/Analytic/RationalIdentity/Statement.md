# Target for rational identity charts

Author: Worker 36.

`Langlands.Analytic.RationalIdentity.IdentityStatement` is a proposition
target over a complete ultrametric normed field `K` and an actual presented
strict affinoid algebra `P`. It asserts three conclusions.

1. For an actual unit denominator `g` and a finite numerator tuple `f`,
   assume that the actual fractions `g⁻¹ * f_i` have bounded monomials in
   `P`: one positive real constant bounds every finite product of powers
   of the fractions. Then a bounded `K`-algebra equivalence from `P` to the
   constructed rational quotient exists. Its forward map is the structural
   base map, its contravariant spectrum homeomorphism is pullback along that
   map, and the rational inequality locus is the entire spectrum of `P`.
2. For denominator one and numerators with norm at most one, a bounded
   equivalence from `P` to the rational quotient exists with forward map
   equal to the structural base map. No monomial-bound hypothesis is needed
   in this specialization.
3. For denominator one and the empty numerator tuple, the same equivalence
   over `P` exists unconditionally.

A bounded algebra equivalence includes bounds in both directions; it is
not asserted to be an isometry. The coefficient field may be trivially
valued, the numerator tuple may be empty, and `P` may be the zero algebra.
There is no normalized-unit-norm or nontrivial-algebra assumption.
Completeness of `K` is explicitly quantified in the target.

This is a derived target about the existing enlarged closed-ideal Tate
quotient. Actual fractions supply a possible evaluation back to `P`;
uniqueness over the base should make that evaluation inverse to the
structural map. For unit-ball numerators, powers can be bounded by
`max 1 ‖1‖`, including in the zero algebra. These are explanations of the
target, not a proof supplied by this statement module.

The source context is Berkovich, *Non-archimedean analytic spaces* (Trieste,
2009), Definition 2.2.1 and Exercise 2.2.2(ii), printed/PDF page 9, with the
strict quotient and bounded morphism conventions in Definitions 2.1.2 and
2.1.11, pages 7–8. The source's rational-domain theorem uses relative series
and arbitrary positive radii. This target treats unit radii and retains an
actual unit and a monomial bound as input. It does not assert that spectral
nonvanishing produces an inverse, or that spectral inequalities imply
power bounds. Relative-series comparison, the full image-containment
factorization property, arbitrary radii, sheaves and atlas gluing remain
separate obligations.

Registered original: `berkovich-2009-trieste-analytic-spaces`, content SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Original URL: https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf.
