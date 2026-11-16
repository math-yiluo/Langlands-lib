# K-level mixed conjugation from its actual central estimate

This internal module adapts the last part of `MoyPrasadMixedConjugation` to the
actual maximal-unramified torus filtration. It assumes the explicit first S1
clause `LocalTorusCommutatorFriendly`, and also an explicit full-depth estimate
for the actual central coordinate of the ordinary/doubled-opposite exchange.
It does not prove that latter estimate.

Ordinary rank-one exchange gives a torus coordinate at half the doubled input
depth. The separate central estimate gives its required full depth. The
negative and positive coordinate bounds of `IntegerMixedConjugation`, with
`MaximalUnramified.exists_order_eq_one`, are compared to this exchange using
injectivity of the opposite-root/centralizer/root product. The resulting
coordinates belong to the two original root blocks and the actual torus
filtration. Including all three factors gives Moy–Prasad membership of the
mixed conjugate. This module keeps the central estimate as an explicit input.
The final S2 composition supplies it through the doubled-root conjugation
module and the published valued rank-one coordinates; it adds no premise to S2.
