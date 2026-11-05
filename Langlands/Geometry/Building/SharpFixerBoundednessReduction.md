# Boundedness from a finite root-product cover

For actual `B : ValuationBuildingData G` over a nonarchimedean local field of
either characteristic and at arbitrary universe `u`,
`SharpFixerFiniteProductBoundednessStatement` is a conditional criterion for
algebraic boundedness of `B.sharpFixer {x}`. It assumes V7, two finite families of
actual relative roots, algebraic boundedness of the actual
`B.apartment.sharpNormalizer {x}`, and containment of the sharp fixer in the
product of the two ordered zero-depth filtration-block ranges followed by that
normalizer. The root families may be empty or contain repetitions; no sign or
enumeration condition is needed for this implication.

The theorem
`isAlgebraicallyBounded_sharpFixer_of_finiteProductCover` proves this criterion
for each pair of families, and `sharpFixerFiniteProductBoundedness` packages it
as the named proposition. These are internal consequences of published
point-topology and actual-root-product results. They neither assert the
finite-product cover nor prove boundedness of the sharp normalizer.

The implemented proof installs exactly the canonical rational-point topology.
Connected reductivity supplies smoothness and hence finite type of `G`.
`KPRootFixerTopology.isCompact_range_orderedFiltrationBlockProduct` makes
each ordered block range compact from V7. The blocks retain their actual
doubled-root factors. The published
`IsAlgebraicallyBounded.isCompact_closure` makes the topological closure of the
sharp normalizer compact from its assumed algebraic boundedness.
Continuous group multiplication makes the product of these three compact
sets compact. The canonical point space is Hausdorff, so this product is closed.
`localFieldAffineBoundedCompactness_proof` gives algebraic boundedness of that
compact product. The assumed cover and inclusion of the normalizer into its
closure then restrict each regular-function bound to the sharp fixer.

The motivation is the final boundedness argument of Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
Proposition 7.3.12 and Corollary 7.3.14, printed pp.249–252 / PDF pp.280–283.
This adapter is not a restatement or proof of those structural results. It
isolates the topological implication once the structural inputs are proved.
The exact corrected apartment premise in `SharpFixerBoundednessStatement`,
including AS5 from the November 1, 2024 corrections
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p.33, remains unchanged.

The exact `SharpFixerBoundednessStatement` and
`CentralizerParahoricIntersectionStatement` remain open. In particular, these
conditional results do not make boundedness follow from compactness of the
root-group generators alone, identify `Z(F)^1` with `Z(F)^0`, or assume a
structural input in the final target.
