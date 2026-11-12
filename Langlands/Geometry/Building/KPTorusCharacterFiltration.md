# Extended-character congruences and a torus filtration

This derived module pulls the actual-character congruence subgroup over a
specified field extension `L/k` back along the published rational scalar
extension map. It proves that the resulting `extendedCharacterCongruence`
family decreases with nonnegative real depth and is preserved by every actual
group-scheme morphism, using `GaloisPointComparison.rationalExtend_map` from
`Langlands.GroupScheme.Rational.ScalarExtensionNaturality`. The rational extension map is injective for an affine
underlying scheme; after an extension that splits a torus, character separation
therefore proves that the pulled-back family is separated.

When `L` is an ultrametric normed field, the valuation is its norm valuation
composed with the normalized negative logarithm with positive scale, the field
inclusion is continuous, the original scheme is affine, and the extended
actual character module is finitely generated, every pulled-back congruence
subgroup is open. Both point groups use exactly their named canonical
`rationalPointTopology` topologies, and units use the induced units topology.
The proof pulls back the logarithmic character openness theorem under the
published continuous rational scalar extension map.

For a finite Galois extension, a valuation `v` on `L`, a real additive valuation
`ω` on `L`, and an affine commutative group scheme `T` over `k`,
`torusCharacterFiltration` is the norm-image subgroup `torusNormIwahori k L v T`
at zero depth and its intersection with `extendedCharacterCongruence k L ω T r`
at every positive depth. Thus its zero group is precisely the chosen norm
subgroup, and its groups decrease with depth. If `L` splits `T`, the family is
separated: membership at all depths implies every extended-character condition
at depth `r+1`, hence at `r`; character separation then gives the identity.
An actual commutative-group morphism preserves the family, by naturality of
the norm image and of the extended-character conditions.

For the canonical rational-point topology over any topological field `k`,
openness of the norm subgroup and of all extended-character congruences implies
openness of this family, by the zero-depth identity and openness of finite
intersections. In particular, suppose `L` is an ultrametric normed field, the
inclusion `k → L` is continuous, the extended actual character module is finitely
generated over the integers, and `ω` is the logarithmic norm valuation with a
positive real scale. Then openness of `torusNormIwahori k L v T` suffices for
openness at every depth. Openness of that norm subgroup remains an explicit
hypothesis of this result; no relation between `v` and `ω` is required.

These are internal constructions from existing scalar congruence, actual
character, rational extension and norm APIs. The basic laws allow arbitrary
`ω` and `v`; no compatibility between the two valuations is silently asserted.
The chosen norm subgroup has the torus Iwahori interpretation when the field
and valuation have the hypotheses of `torusNormIwahori`. No splitting-field
independence of positive groups, induced-torus comparison, root compatibility,
or full centralizer-filtration existence is established here.
