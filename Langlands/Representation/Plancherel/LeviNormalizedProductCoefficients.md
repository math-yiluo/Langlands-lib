# Actual product coefficients in the positive Levi normalization

This derived adapter puts the existing product-induced coefficient map on the
actual positive Levi-normalized function space. It proves the diagonal integral
formula, its pure tensor specialization, equivariance and equality of its image
with the existing smooth coefficient space. It reuses the published
`ProductInducedCoefficients` integral duality and convergence results.

The original source is J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)*, DOI 10.1017/S1474748003000082,
I.3, printed p.243 (PDF p.9), and V.1, printed p.288 (PDF p.54).
The registered source is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
I.3 defines the positive Levi half-modulus convention. V.1 defines
`L(ω,P) = I_(P×P)^(G×G)(E ⊗ Ě)` and its coefficient map through the
induced representation and its smooth dual. The construction here is an
internal normalization transport of the existing actual integral coefficient
map; it does not assume the integral formula as a hypothesis.

## Inputs and scope

`G : Type uG` is locally compact and nonarchimedean.
`h : IsSemidirectDecomposition P M U` is actual subgroup data and `U` is
closed. `A : SmoothRep ℂ M` has an independent carrier universe `uV`.
The source coefficient object and diagonal contraction require only these
inputs. The full-parabolic comparison additionally assumes second countability
of `G` and `huni : IsUnimodularModulus U hU`. Product radical unimodularity is
derived by `isUnimodularModulus_prod`. This comparison does not need compact
parabolic quotient, admissibility or integration data.

For integrability, retain the existing theorem's explicit hypotheses:
compactness of `Induction.LeftQuotient P`, `T2Space G`, Borel measurable
structure, local compactness and closedness of `P`, trivial ambient modular
character, and equality of the actual modular character on `P` with the
positive radical Haar modulus. The last equality is the displayed `hmod`;
it is distinct from radical unimodularity `huni`.

The coefficient map and its formulas further retain continuity of the actual
Levi projection `h.projection` and admissibility of `A`. These hypotheses
allow the existing integral duality equivalence. No irreducibility of `A` or
of its induction is used. The generic subgroup framework is broader than the
source's reductive setting; no unconditional rational-point realization or
Plancherel conclusion is claimed.

## Actual coefficient functions and normalization

`leviProductInducedCoefficientObject` is the existing
`DynamicNormalization.leviTwistedInductionFunctor` for the literal product parabolic and product
Levi, applied to `productLeviObject A A.contragredient`.
`leviProductInducedCoefficientIntegrand` contracts its value at `(k*g,k)`
using `TensorProduct.lift (smoothDualPairing A.representation).flip`.
It is linear in the induced function.

`productInducedCoefficientLeviEquiv` specializes the existing normalization
comparison to the product decomposition and uses derived product radical
unimodularity. It is an actual representation equivalence and preserves every
function value. The object and comparison are abbreviations for those existing
constructions. The evaluation theorem applies the generic normalization
evaluation law. The forward and inverse integrand comparisons apply the
corresponding generic evaluation laws and then the fixed linear contraction at
each argument.

`leviProductInducedCoefficientIntegrand_integrable` applies the published
full-parabolic integrability theorem to the inverse normalization image.
The diagonal contraction is unchanged, so this proves convergence for each
actual source-normalized induced function. This theorem requires neither
admissibility nor continuity of the Levi projection.

## Coefficient map and formulas

`leviProductInducedCoefficientMap` composes the existing
`productInducedCoefficientMap` with the inverse normalization comparison.
The comparison theorem cancels inverse and forward equivalences, proving that
the two maps agree on corresponding actual functions.

`leviProductInducedCoefficientMap_integral` applies the existing all-vector
integral formula to the inverse image. Value preservation makes its integrand
the literal source-normalized diagonal contraction. Thus the formula does not
depend on a chosen tensor expansion.

`leviProductInducedCoefficientMap_tmul` substitutes the proved
`leviNormalizedProductInductionTensorEquiv_tmul_eval` into that integral.
For source-normalized functions `f` and `fdual` it gives
`∫ k, fdual(k)(f(k*g))` against the same fixed
`normalizedInductionBruhatMeasure hP hG`. The integration variable is the
existing top-subgroup model of `G` used by that quotient-integration measure.

`leviProductInducedCoefficientMap_action` uses equivariance of the inverse
normalization equivalence and the published full-parabolic coefficient action
law. The resulting argument is `x.2⁻¹ * g * x.1`, preserving the original
multiplication order. Finally, `range_leviProductInducedCoefficientMap` uses
the forward and inverse normalization maps to prove both inclusions between
its range and the existing product coefficient range. The existing range
theorem then identifies its image with the actual coefficient space of the
canonical full-parabolic normalized induction.
