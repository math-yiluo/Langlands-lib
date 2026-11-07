# The compatible affine atlas for integral scheme pushouts

This internal construction supplies `CompatibleAffinePushoutAtlas` for actual schemes `X`, `Y`, and `Z`, a closed immersion `i : Z ⟶ X`, an integral map `j : Z ⟶ Y`, and exactly the displayed fibre-affine-neighborhood hypothesis. The index is all `CompatibleAffinePairs i j`, so every compatible pair of affine opens occurs. The coverage results of `IntegralSchemePushoutAffineCover` supply coverage of both schemes.

For each compatible pair `U`, `V`, the common source is the open subscheme associated to `i⁻¹(U) = j⁻¹(V)`. It is affine because the preimage of an affine open under a closed immersion is affine. The restricted first map is a closed immersion. The restricted second map is integral: the compatibility equality identifies its source isomorphically with the full inverse image of `V`, and target restriction preserves integrality. `AffineSpan` then supplies the affine model, both actual cocone maps, and the locally ringed pushout property. It also gives an integral left model map and a closed-immersion right model map.

Together with the preceding global construction and descent lemmas, this atlas constructs a scheme pushout and proves integrality and closedness of its legs. The final global cartesian-square conclusion still requires the separate affine cartesian-square result.
