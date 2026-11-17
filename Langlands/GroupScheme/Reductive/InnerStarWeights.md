# Integral weights of inner simply connected groups are star fixed

This internal deduction supplies the weight-fixedness prerequisite for the
actual Tits obstruction construction. It concerns the actual character and
cocharacter lattices of an actual split maximal torus after field extension.
The unit constructs no Brauer class and makes no descent-effectivity claim.

For an affine, locally finite type group scheme `G` over any field `k`, and
supplied `GaloisPinningData k K G`, `IsInnerStarAction` says that every element
of `K ≃ₐ[k] K` fixes every simple vertex under the supplied star action.
`IsStarFixedWeight lam` says that this same action fixes the actual integral
character `lam`. These are properties of the existing action, with no
additional supplied maps.

If `G` is simply connected, `corootSpan_eq_top_of_simplyConnected` first
applies the published field-extension theorem to `G_K`, then the published
necessity direction of the split coroot criterion to the actual torus,
inclusion, reduced root datum and base in the supplied pinning. Thus the
coroots span the actual integral cocharacter lattice. This span is a proved
consequence, not an extra hypothesis.

The published `fundamentalWeightBasis` is then an integral basis of the
entire character lattice. The published
`fundamentalWeightBasis_fixed_of_based` shows that a based automorphism
fixing a vertex fixes its fundamental weight.
`starAction_fundamentalWeight_of_inner` applies this result.
`starAction_weight_of_inner` uses equality of linear maps on this integral
basis to prove that the weight map is the identity. This also covers an
empty simple-root base: the integral basis argument remains valid in rank
zero. `isStarFixedWeight_of_inner` packages the result for each character.

`IsInnerAbsoluteStarAction` explicitly uses `absoluteStarAction` for the
canonical pinning over `SeparableClosure k`. The theorem
`absoluteStarAction_weight_of_inner` proves that this full absolute action
fixes every integral character. The Prop-valued uniform target
`InnerSimplyConnectedStarFixedWeightsStatement` and its proof
`innerSimplyConnectedStarFixedWeights` allow any supplied pinning over the
same separable closure, and quantify over every element of the full absolute
Galois group. They require only simple connectedness and the vertex
innerness hypothesis.

The mathematical context is Tits, *Representations lineaires irreductibles
d'un groupe reductif sur un corps quelconque* (1971), section 3.1, printed
pp.202–203, which defines the star action on the weight lattice and its
fixed weights. Source `provided-24a63a63d1d1f52de3bb06c78f1f0b8837e492ae9eb6ee738ba647284515e9d2`,
content SHA-256
`dbab2ec31991b639ce5461e2fe0713ff4bc5f4b9f01dfcdcc24e1a0794c5edb9`.
The present implication is an internal deduction through the published
integral fundamental-weight basis, rather than a verbatim theorem of that
source. The source's representation obstruction and its additivity are
separate construction obligations.

All declarations are uniform in `k : Type u` and `K : Type u` for every
`u`. There is no restriction on characteristic, perfection, Dynkin type or
smoothness of the scheme-theoretic centre. No centre points are used.
