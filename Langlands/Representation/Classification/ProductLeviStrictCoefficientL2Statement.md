# Square integrability of coefficients from strict fundamental bounds

Author: Worker 19.

`Langlands.GLProductLeviStrictCoefficientL2Statement.{uF,uV}` is a closed
proposition definition. It is an internal interface for the exponent-two
summation step of the strict Jacquet criterion. This module supplies no proof.

For any prime, finite p-adic field `F`, compatible topological data `T`,
rank `n` and block shape `C`, put `M = C.Levi F.Carrier`. Give
`M ⧸ Subgroup.center M` an arbitrary Borel measurable structure and a Haar
measure `μ`. If `ρ` is admissible and satisfies
`ProductLeviSquareIntegrable.StrictFundHypothesis T C ρ`, then for every
`c : UnitaryCentralCharacter ρ`, smooth-dual vector `ℓ` and vector `v`,
the descended absolute coefficient `c.coefficientNorm ℓ v` belongs to
`L²(μ)`.

The field and carrier universes are independent. There is no irreducibility,
nontriviality, finite-length or finite-dimensionality assumption. The statement
also covers rank zero and an empty fundamental index set. It assumes the
published `CartanCellCountStatement` explicitly, so the resulting summation
lemma can be used with any proof of that count. The Library already contains
`GeneralLinear.CartanQuotient.cartanCellCount`.

The strict hypothesis quantifies every uniform generalized eigencharacter on
each fundamental upper refined Jacquet module, without an open-kernel premise,
and requires norm strictly below one at its fundamental uniformizer tuple.
This statement neither proves that hypothesis from whole-chamber bounds nor
asserts existence of a unitary central character. Both are separate bridges
needed by consumers.

The provenance is internal: this isolates the exponent-two specialization of
the published `ProductLeviSquareIntegrable.memLp_of_strict` argument in
[`ProductLeviSquareIntegrableLpProof`](ProductLeviSquareIntegrableLpProof.md).
Its inputs are the strict coefficient bound
`cb * ∏ j, delta(lam j)^(1/2 + ε)` with `ε > 0`, the inverse-modulus cell-volume
bound, and finite geometric-lattice summability. At exponent two the remaining
geometric ratio is `fundWeight^(2*ε)`, which is strictly below one.
These are references to existing Library mathematics and an intended proof
route, rather than additional hypotheses of the displayed proposition.

The interface is intended for both the arbitrary-admissible strict GL
criterion and the product-Levi sufficiency criterion. It uses no segment or
square-integrable classification, exhaustion, weakly-critical support,
tempered support, tempered unitarity or genericity result.
