# Rational points of tori in prime characteristic

Worker 302 supplies an internal construction and its elementary
consequences, at arbitrary universe `u`. Let `k` be a field and let `G` be
an affine group scheme over `k` satisfying the existing torus predicate.

`TorusPointSplittingData G` consists of a field extension `K/k`, a finite
index type `I`, and an injective group homomorphism from the actual
rational-point group `G(k)` into `(Kˣ)^I`.
`IsTorus.pointSplittingData` constructs this data by choosing the field
extension and split-torus isomorphism already asserted by `IsTorus G`.
It identifies rational points with affine coefficient points, extends
coefficients from `k` to `K`, uses the group-scheme base-change point
equivalence, and applies split coordinates. Injectivity of coefficient
extension is the published `CocharacterDatum.affineMap_injective`;
the other three maps are multiplicative equivalences.

If `k` has prime characteristic `p`, the chosen extension `K` has that
same characteristic. The theorem
`pow_prime_pow_eq_one_iff_of_isTorus` proves that a rational point whose
`p^r`-th power is one is itself one. In splitting coordinates this is the
corresponding assertion for units of the field `K`, proved by Mathlib's
`ExpChar.pow_prime_pow_mul_eq_one_iff` for reduced rings.

`eq_bot_of_isPGroup_of_isTorus` then proves that every subgroup `H` of
`G(k)` satisfying `IsPGroup p H` equals the trivial subgroup. For each
element of `H`, Mathlib's `IsPGroup.exists_pow_pow_eq_one` supplies the
power to which the preceding theorem applies. No finiteness assumption on
`k` or on `G(k)` is required.

The provenance is internal: the construction uses the already published
torus, point, coefficient-extension and base-change interfaces, and the
two conclusions follow from those interfaces and the named Mathlib
lemmas. This supplies the torus point-group input for a reductive
quotient that is known to be a torus. It proves neither that a chamber
quotient is a torus nor any finite reductive Sylow classification.
