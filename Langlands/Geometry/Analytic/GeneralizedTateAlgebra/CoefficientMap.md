# Bounded coefficient maps on weighted restricted series

Author: Worker 56.

For a positive real polyradius `r` and ultrametric normed commutative rings
`A` and `B`, a bounded unital ring homomorphism `φ : A → B` induces the
actual coefficientwise map

\[
\sum_d a_d T^d \longmapsto \sum_d \varphi(a_d)T^d
\]

between `GeneralizedTateAlgebra r A` and `GeneralizedTateAlgebra r B`.
`mapCoefficientsRingHom` restricts Mathlib's `MvPowerSeries.map` to the
published weighted restricted subalgebras; `mapCoefficients` bundles the
same ring map with its proved boundedness. The coefficient formula is
`coeff_mapCoefficients`, and `series_mapCoefficients` identifies the
underlying formal series.

The construction uses the cofinite filter on finitely supported exponents,
just as `GeneralizedTateAlgebra.Definitions` does. If
`‖φ(a)‖ ≤ C * ‖a‖` for all coefficients and `C ≥ 0`, then the induced map
satisfies `‖mapCoefficients r φ f‖ ≤ C * ‖f‖` for every series `f`.
This preserves the supplied constant exactly, including a zero constant
when its hypothesis holds. In particular, a contractive coefficient map
induces a contractive series map. A positive bound exists by the input
`BoundedRingHom` hypothesis and supplies boundedness of the bundled map.

The proofs first multiply the coefficient estimate by the positive
monomial weight. Squeezing between zero and a constant multiple of the
original weighted coefficient sequence proves restrictedness. This first
lemma does not need the target ultrametric hypothesis. The weighted
coefficient characterization of the Gauss norm then gives the same norm
bound. The ring laws come from the existing formal-series ring map.

Identity and composition of coefficient maps give identity and composition
of the bundled series maps. The map takes a coefficient monomial to the
monomial with its coefficient mapped, commutes with the respective constant
inclusions, and fixes the variable series. Injectivity on coefficients
implies injectivity on series by coefficient extensionality. If the
coefficient map preserves norms, the two weighted coefficient bounds give
equality of the series norms; a coefficient isometry therefore induces a
series isometry. These conclusions are proved in this file.

The original motivation is Berkovich, *Non-Archimedean analytic spaces*,
Trieste lectures (2009), Definition 2.1.6(i), printed/PDF page 8, which
defines relative finite-variable series with weighted coefficient decay
and the weighted supremum norm. That page was read directly. Registered
original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`, retained at
`/home/taskhub/central-library/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009.pdf`.

This coefficient-map construction and its laws are derived consequences
of the displayed series formula and the published normed-series
construction, rather than a separately quoted theorem from that source.
Mathlib's `MvPowerSeries.map`, `coeff_map`, `map_monomial`, and `map_C`
provide the underlying algebraic operations. As in the published
`GeneralizedTateAlgebra.Definitions`, Lean permits arbitrary variable types
and ultrametric normed commutative coefficient rings, extending the
source's finite-variable Banach-affinoid setting. No completeness,
nontriviality, norm-one condition, or value-group condition on radii is
needed here. Empty variable types and zero coefficient rings are allowed
whenever the input unital homomorphism exists.

This unit constructs bounded ring maps. Additional common-base scalar
structures, relative quotient identifications, surjectivity of coefficient
maps on restricted series, presentation independence, and analytic sites
remain separate obligations.
