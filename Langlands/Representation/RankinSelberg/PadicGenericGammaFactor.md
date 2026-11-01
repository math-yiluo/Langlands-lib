# Constructed gamma factors of generic p-adic pairs

Author: Worker 31.

This module constructs actual rational-function gamma units from the existing
`Whittaker.IsGeneric` hypotheses on two representations and a supplied
self-dual additive Haar measure. The field and two carrier universes
`uF,uV,uW` are independent. The field is any `PadicField p` for a prime `p`;
all ranks are positive successors, including rank one. Coefficients are
complex, and no topology or finite-dimensionality condition is imposed on
the representation carriers.

## Derived provenance and normalization

This is an assembly of the published `GenericModel`,
`WhittakerTypeGammaConstructionInputProof` and `GammaFromWhittakerType`
constructions. The generic-to-type bridge uses the proved multiplicity
theorem to supply full Whittaker type: admissibility, group-algebra finite
generation and the one-dimensional functional space. Full inverse-standard
type of the second representation is obtained by the existing character
transport. The construction-input proof supplies the original and actual
inverse-transpose analytic conclusions and uniform epsilon existence from
the published equal- and unequal-rank analytic and functional-equation
theorems. Those conclusions are derived here through that proof, rather than
added as hypotheses to the generic constructors.

The original normalization is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
Section 2.1, printed pp.385–386; Theorem 2.7, printed pp.390–391; and
Section 2.12, printed p.403. Registered source:
`jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
These passages give Whittaker type and its model, the normalized integral
equations, and the larger-rank-first convention for L and epsilon. The gamma
convention is the derived expression

\[
 \gamma(s)=\epsilon(s)\frac{L(1-s,\text{inverse-transpose pair})}
                              {L(s,\text{original pair})}.
\]

The existing gamma construction implements this ratio by rational functions,
with the central-character sign outside gamma in the functional equation.
This module reuses that construction and its universal relation; it proves
no additional formula comparing independently selected L or epsilon data.
JPSS does not separately define gamma in Section 2.12: the inherited
larger-rank-first gamma convention follows from that ratio.

## Ordered construction

`genericPairGammaConstructionInput` assumes `n ≤ r` for ranks `r+1,n+1`.
It applies `padicPairGammaConstructionInput_of_whittakerType` to the
standard and inverse-standard types derived from genericity. The supplied
Haar measure and self-duality proof are packaged as the existing
`PadicAbelian.SelfDualHaar`; no self-dual measure is selected here.

`genericPairGammaFactor` takes the unit returned by
`padicPairGammaFactorOfWhittakerType`. Its theorem
`genericPairGammaFactor_isPadic` gives exactly
`IsPadicPairGammaFactor` for that rational function. This relation includes
compatible quotient-measure existence, nonzero functional witnesses, and
the gamma functional equation for every compatible quotient measure and
every pair of nonzero functionals. The equal-rank equation retains every
Schwartz–Bruhat test and its Fourier transform. The unequal-rank equation
retains every permitted rectangular block and its complementary transformed
block. The imported construction retains the model scalar at minus one
and the Weyl translation. Thus the specification is nonvacuous and does not
depend on a chosen functional or quotient measure.

`genericPairGammaFactor_eq` identifies this factor with every certified
rational function by the published uniqueness theorem.
`isPadicPairGammaFactor_iff_eq_genericPairGammaFactor` gives the resulting
two-way characterization. The residue cardinality is the actual canonical
one, and the absolute value is the canonical normalized absolute value.

## Both rank orders and spectral values

`genericSymmetricGammaConstructionInput` applies the published closed
Whittaker-type input theorem to the types derived from the two generic
representations. It covers both rank orders.
`genericSymmetricGammaFactor` selects the ordered constructor on `(π,σ)`
when `n ≤ r`, and on `(σ,π)` otherwise. Equal ranks retain the input order.
The `_of_le` and `_of_lt` lemmas give these branch equalities.
`genericSymmetricGammaFactor_isPadic` proves the existing
`IsPadicSymmetricGammaFactor` specification, and the `_eq` and `iff_eq`
lemmas give uniqueness and characterization. A further equality identifies
the unit with `padicSymmetricGammaFactorOfWhittakerType` at the derived
input. These are applications of the existing rank convention, with no
additional rank-exchange identity.

For each ordered or symmetric factor, `genericPairGammaRegularDomain` or
`genericSymmetricGammaRegularDomain` is the set of `s : ℂ` at which the
factor's reduced rational denominator does not vanish at
`spectralPoint q s = q^(-s)`. The corresponding `GammaValue` evaluates the
rational function at that spectral point, taking a parameter in this
domain. Its `_eq` lemma records the exact evaluation. Reduced denominators
retain removable cancellations. The values are complex numbers; a
rational-function unit can have spectral zeros, so these are not asserted
to be complex units.

The module installs the canonical normed-field and valuative local-field
structures and Borel measurable structure. Its private nonarchimedean
additive-group helper uses the open valuation-integer submodule basis,
which supplies the total-disconnectedness needed by the existing
self-duality interface. The local instances have distinct names and add
no additional field or measure hypothesis.

Self-dual Haar existence remains a supplied input. Character-change laws,
twist laws, multiplicativity, tempered product and pole theorems,
smooth-contragredient comparisons, representation-class descent and
nongeneric constructions remain separate obligations. This module contains
no proof holes or new axioms.
