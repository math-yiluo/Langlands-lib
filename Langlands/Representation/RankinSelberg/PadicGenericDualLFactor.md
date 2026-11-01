# Constructed inverse-transpose L-factors of generic p-adic pairs

Author: Worker 31.

This module constructs the normalized polynomial and rational-function L-unit
of the actual `inverseTransposePullback` pair, with character `ψ.scale (-1)`
and the same supplied additive Haar measure `ν`. Its assumptions are genericity
of the two original representations. The field and both representation
carriers retain independent universes `uF,uV,uW`; the ranks are arbitrary
positive successors, including rank one. The field topology, residue
cardinality and absolute value are those of `F.canonicalTopologicalData`.
Coefficients are complex. No self-duality assumption on the measure is needed.
Here genericity means irreducibility, admissibility (including smoothness)
and a nonzero standard Whittaker functional. The representation carriers
need only their complex module structures.

## Construction and implemented proofs

The supporting theorem `padicPairLPolynomial_isPadic` gives the full canonical
`IsPadicPairLPolynomial` specification for the published supplied-topology
`padicPairLPolynomial` constructor at a pair of full Whittaker type. It
constructs the compatible quotient-measure witness and uses
`padicPairLPolynomial_spec` for every compatible measure. Thus its universal
measure specification has an actual witness.

`genericPairDualLPolynomial` and `genericPairDualLFactor` assume `n ≤ r` for
the original ranks `r+1,n+1`. They apply the existing actual polynomial and
unit constructors to the inverse-transpose pair and the inverse character.
The full types needed in the two slots follow from
`isOfWhittakerType_of_isGeneric`, `isOfInverseWhittakerType_of_isGeneric`,
`isOfWhittakerType_firstDual` and `isOfWhittakerType_secondDual`. No separate
genericity premise on the transformed representations, analytic premise or
polynomial-existence premise is supplied.

`genericPairDualLPolynomial_isPadic` proves the unchanged intrinsic
specification on that transformed pair. It retains every compatible quotient
measure and every permitted unequal-rank block. The constant coefficient is
one; uniqueness compares the selected polynomial with every polynomial
satisfying this intrinsic relation. `coe_genericPairDualLFactor` identifies
the rational unit with the reciprocal of the polynomial embedded in
`RatFunc ℂ`, and `genericPairDualLFactor_eq` gives this description for every
certified polynomial.

`genericSymmetricDualLPolynomial` and `genericSymmetricDualLFactor` use the
larger-rank-first constructor in the original order when `n ≤ r` and with
both representations, universes and genericity proofs exchanged otherwise.
At equal rank the input order is retained. Their branch lemmas, full
`IsPadicSymmetricLPolynomial` specification, constant coefficient, uniqueness
and reciprocal formulas follow from those of the selected ordered branch.

## Derived provenance and source

This is derived composition of `PadicPairLFactor`, `GenericModel`,
`GammaFromWhittakerType`, `DualWhittakerType` and the intrinsic rank-order
relations in `PadicPairFactors`. The analytic and common-generator existence
results are already proved dependencies of `PadicPairLFactor`. The present
module makes their application to the actual inverse-transpose pair explicit.
It does not identify that pair with a smooth contragredient or add a factor law.
Distinctly named local instances install the canonical normed field, valuation,
local-field structure and Borel measurable space; these add no hypotheses.

The original source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Section 2.1, printed p.386, formula (4) (retained PDF p.21), gives the
Weyl-translated inverse-transpose model and inverse character. Theorem 2.7,
printed pp.390–391 (PDF pp.25–26), gives the normalized reciprocal generator,
including the inverse-transpose pair. Section 2.12, printed p.403 (PDF p.38),
gives the larger-rank-first L convention. These original pages were read
visually for this construction; no JPSS-specific errata file was found in
the inspected project literature or current Library notes.

The formal variable remains `X=q^(-s)`. This module constructs the dual-pair
L-factor in that variable; a reflection to `1-s`, comparison of independently
constructed gamma and epsilon factors, character-change or twist laws,
equal-rank interchange and nongeneric extensions are separate work.
