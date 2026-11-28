# A continuous equivariant retraction onto the norm-one adelic group

Let `G` be a connected reductive group over a number field `F`. The norm-one group `G(𝔸_F)¹` is
the common kernel of the absolute values `|χ(x)|` of the rational characters `χ` of `G`. The module
`Langlands.Global.AdelicNormOneRetraction` proves:

`exists_normOneRetraction F G hG`: there is a continuous map `r : G(𝔸_F) → G(𝔸_F)¹` with
`r(n) = n` for `n ∈ G(𝔸_F)¹`, `r(g x) = g r(x)` and `r(x g) = r(x) g` for `g ∈ G(𝔸_F)¹`.

**Construction.** Choose a split component, a central split torus `T` of `G` defined over `F`
(`exists_isSplitComponent`). The restriction of rational characters from `G` to `T` is injective
(`characterRestrict_injective_of_centralSplitTorusCharacter`) with image of finite index
(`characterRestrictionFiniteIndexStatement`). In split coordinates, the intrinsic positive
subgroup `intrinsicSubgroup F T` of `T(𝔸_F)` consists of one positive real scalar per coordinate,
embedded diagonally at all infinite places with identity components at all finite places.
This is `subgroup_eq_intrinsicSubgroup` with scalar coordinates given by `PositiveRealIdeles.full`.
The normalized ambient character logarithm identifies this subgroup with the real character
dual of `G` via `positiveAmbientLogEquiv`. The map `positiveFactor` applies the inverse equivalence
to the character logarithm of `x`. Write `a(x)` for the image of `positiveFactor x` in `G(𝔸_F)`
under `positivePointMap`. The retraction is

`normOneRightFactor x = x · a(x)⁻¹`,

which lies in `G(𝔸_F)¹` because `x` and `a(x)` have the same character logarithm. This map is
continuous (`continuous_normOneRightFactor`) and fixes `G(𝔸_F)¹` (`normOneRightFactor_normOne`).
For `g ∈ G(𝔸_F)¹`, the logarithms of `g x` and `x g` agree with that of `x`, so their positive
factors agree with `a(x)`. This gives left equivariance (`normOneRightFactor_mul_left`). Centrality
of `T` lets `a(x)` commute with `g` in the right equivariance proof (`normOneRightFactor_mul_right`).

Composing a continuous left `G(F)`-invariant function on `G(𝔸_F)¹` with `r` gives a continuous
left `G(F)`-invariant function on `G(𝔸_F)` with the same restriction to `G(𝔸_F)¹`; see
`Langlands.Global.AdelicNormOneExtension`.
