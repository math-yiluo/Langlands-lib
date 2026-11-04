# The remaining first-chart normalization as compact-open masses

This internal derived construction supplies the first product normalization
needed by `StandardIntertwiningLocallyNormalizedComposition`. The source
motivation is the ordered product and iterated integration in Waldspurger
(2003), IV.1, printed p.279 / PDF p.45, and distance-additive composition
IV.1(12), printed p.283 / PDF p.49. The result retains actual local geometry
and a genuine source-measure compatibility condition; it does not infer these
from the existence of the charts.

## Actual subgroup copy and measure transport

Retain `D : OrderedSubgroupFactorization U₀ U₁ U₂ V W`, on a group in
arbitrary universe. The actual subgroup `V.subgroupOf U₁` is identified
with `V` by `firstComplementEquiv`, using `D.first_le`.
`firstSubgroupProduct` is `D.first` expressed on the actual subgroups
`U₀.subgroupOf U₁` and `V.subgroupOf U₁`. Its value is their literal product
in that order in `U₁`; no commutativity, normality or product-group
homomorphism is asserted.

For a specified measure `μV`, `firstComplementMeasure` is its pushforward
by the inverse continuous group equivalence to `V.subgroupOf U₁`.
Regularity, the Haar property, S-finiteness and right invariance transport
from the corresponding properties of `μV`. Pushing this measure back by
`firstComplementEquiv` gives exactly `μV`, without a scalar.
The regularity of `μI₁₀.prod μV` also transports to the product with the
actual subgroup copy; it is proved using the product pushforward formula
and the product homeomorphism. Both individual and product Borel structures
and both S-finiteness hypotheses used by this transport are explicit.
No subgroup measure is obtained by restricting ambient Haar measure.

## From local mass compatibility to the full first product identity

`measurePreserving_first_of_compactOpenMass` uses a Hausdorff topological
ambient group and locally compact `U₁`; regular Haar `μU₁`; regular
two-sided S-finite Haar measures `μI₁₀` and `μV`; regularity of their
product; the displayed individual, product and quotient Borel structures;
a compatible Weil measure on `(U₀ ∩ U₁) \ U₁`; and closedness of the actual
intersection.

Supply compact open subgroups `R` of `U₁` and `A` of `V.subgroupOf U₁`,
with the actual local product image

`firstSubgroupProduct '' (((U₀ ∩ U₁) ∩ R) × A) = R`.

The measure comparison premise is the concrete equality

`μU₁(R) = μI₁₀((U₀ ∩ U₁) ∩ R) * firstComplementMeasure μV (A)`.

This concerns one compact-open mass and is not a global product-preservation
assumption. The local image identity gives the corresponding quotient orbit
identity. The existing compatible-Weil compact-open comparison then supplies
the full product-preservation theorem on the actual two subgroups. Applying
the complement equivalence and its exact return-transport formula yields

`MeasurePreserving D.first (μI₁₀.prod μV) μU₁`.

## Application to the constructed first-complement measure

`measurePreserving_first_normalized_of_compactOpenMass` uses precisely
`μV = D.intersectionNormalizedFactor μI₂₁ μH μK S B` from the preceding
intersection construction. It retains locally compact Hausdorff ambient
group, closed `U₀` and `U₁`, regular Haar `μU₁`, regular two-sided S-finite
Haar `μI₁₀`, Haar `μI₂₁` and `μH`, regular two-sided S-finite Haar `μK`,
compactness of `S` and `B`, regularity of `μI₁₀.prod μV`, the displayed
Borel structures and the same first-chart local geometry and mass equality.
The proof derives closedness of the nested intersection and the local
compactness needed for the first chart, establishes that the constructed
`μV` is Haar, and applies the generic comparison above.

The conclusion supplies the remaining first-chart product identity to
`measurePreserving_quotientCoordinates_of_localProducts` or
`comp_hasIntegral_of_localProducts` in the preceding module. No global
product normalization is assumed by the two theorems here. The actual
compact-open geometries, compatible Weil measures, product regularity and
mass equality remain application obligations. In particular the mass
equality for separately specified source Haar measures, the reductive
charts and root-distance geometry, integral convergence and rational
continuation remain open. No whole-task Plancherel condition is closed.
