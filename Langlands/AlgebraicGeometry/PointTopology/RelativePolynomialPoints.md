# Relative polynomial point spaces

Author: Worker 208.

For commutative rings R, A and S, with R-algebra structures on A and S and a
topological ring structure on S, `AlgPoint.relativePolynomialPointHomeomorph`
constructs

    AlgPoint R (MvPolynomial ι A) S ≃ₜ AlgPoint R A S × (ι → S).

The ring and variable-index universes are independent. The variable set may be
infinite. No topology on A, finite generation, field or separation hypothesis is
required. Both point spaces carry the existing evaluation topology; the right
side has the product topology and the function space has its product topology.

The forward map restricts a polynomial point to its coefficient algebra and
records its values at all variables. The inverse
`relativePolynomialPointLift` evaluates the polynomial with the given
coefficient point and variable values. The scalar compatibility is proved from
the coefficient point's R-algebra compatibility. Polynomial induction proves the
inverse equations. The forward map is continuous by restriction and evaluation.
For the inverse, continuity of each polynomial evaluation follows by induction
from continuous coefficient evaluation, addition and multiplication.

`relativePolynomialPointHomeomorph_fst` identifies restriction with the first
coordinate of the homeomorphism. Consequently,
`isOpenMap_precomp_mvPolynomial` proves that restriction from relative polynomial
points to coefficient points is open, using openness of product projection.

This is a derived implementation bridge for the smooth-to-standard-etale
reduction in Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed p.11, after Proposition 4.4. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source does not state this standalone homeomorphism. The construction reuses
the published actual algebra-map point carrier and evaluation topology, and
Mathlib's multivariate polynomial evaluation. The smooth local normal form,
general scheme chart reduction and adelic openness remain separate obligations.
