# Limit descent from an actual scheme pullback over a target atlas

This internal supporting construction retains the actual geometric data of a
cartesian target-atlas square while placing no representability premise on the
original space morphism. It uses the published effective-descent proposition
as an explicit premise and does not prove that proposition.

`SchemeTargetAtlas` consists of two actual schemes over the base, a surjective
étale target atlas, a scheme morphism between the schemes, a map from its source
to the source space, and the cartesian square on whole presheaves.
`of_presheafIso` constructs these data from a whole-presheaf representation of
any given space pullback. Fullness of scheme Yoneda recovers the actual scheme
projection, and transport of the given cartesian square supplies its square.

`baseChange` restricts the square and transfers both scheme corners through the
natural scheme Yoneda base-change isomorphisms. Étaleness and surjectivity of
the target atlas survive this restriction.

`property_iff` explicitly assumes `EtaleAtlasPropertyEffectivity P`.
The forward direction uses the definition of the relative property on the
given cartesian square. The reverse direction applies precisely that
effective-descent premise. `property_baseChange_iff` also assumes stability of
the scheme property under base change. It applies this test after restriction
and identifies the scheme projection with the scheme limit-descent convention
using the published arrow comparison.

`property_limit_iff` assumes both `EtaleAtlasPropertyEffectivity P` and
`SchemeStructuralPropertyDescent P`. The original scheme source and target
structure morphisms are each locally finitely presented, quasi-compact and
quasi-separated. For an arbitrary cofiltered diagram of affine schemes and an
original stage, it proves that the space property at the limit is equivalent
to the property at some later stage. Its forward proof restricts the diagram to
the cofinal category of arrows into the original stage, applies the scheme
descent input to the fixed scheme morphism, and applies effective descent at
the resulting stage. The reverse proof uses base change and its natural
comparison with the direct limiting-cone projection.

The provenance is the pullback universal property, full scheme Yoneda, the
published scheme/base-change comparisons, and the two displayed proposition
premises. This extends the fixed represented-atlas reduction by allowing
effectivity to supply representability together with the property. It does not
assert existence of such an atlas at the original stage, discharge either
premise, or prove the unrestricted eight-property limit-descent theorem.
