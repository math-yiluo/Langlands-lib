# Compatible split components at the fixed torus

The internal adapter `exists_compatibleStandardSplitComponent` proves existence of the actual algebraic component requested by `IsCompatibleStandardSplitComponent`, before choosing any compact-open subgroup. It uses the published `standardLeviSplitComponentStatement` proof, retains the actual standard Levi representative and inclusion, and proves that its factor through the prescribed ambient torus is a split subtorus with `IsSplitSubtorus.of_comp`.

All group schemes, maps and connected-reductivity properties are supplied by that published theorem. This adapter introduces no existence assumption or building premise and does not choose another maximal torus. It proves no Iwahori or contraction property. Its provenance is the direct repackaging of those existing Library results into the fixed target predicate.
