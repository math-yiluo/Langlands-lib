# The same geometric fibre over two scheme bases

For an arbitrary scheme morphism `g : T → S`, this internal supporting module
constructs a homeomorphism between the points of a fibre of a base-changed
algebraic-space morphism over `T` and the points of the identical fibre
viewed over `S`. It also proves compatibility with the projection to the
represented target scheme. No finiteness, separation or representability
hypothesis is imposed on the algebraic-space morphism.

The map `forgetBaseYoneda g U` is monic: it sends a morphism over `T` to its
same underlying scheme morphism over `S`. Its naturality square for every
morphism `U → V` of schemes over `T` is cartesian. The proof checks the
square on each represented test. A map over `S` to `U`, together with a
map over `T` to `V` whose underlying composite agrees, has a unique lift
over `T`, since `U → V` respects the `T` structure maps.

For `y : h_V → restrictPresheaf g Y`, `originalBaseChart g y` is the chart
`h_(V over S) → Y` with the same Yoneda section. Restricting it and
precomposing with `forgetBaseYoneda g V` recovers `y` exactly. For any
presheaf morphism `f : X → Y`, `fibreRestrictionMap g f y` is the actual
map

`X_T ×_(Y_T) h_V → restrictPresheaf g (X ×_Y h_(V over S))`.

It is defined by the universal property of the restricted pullback. Its
first projection is the fibre's first projection, and its second is the
fibre's second projection followed by `forgetBaseYoneda g V`. Pullback
cancellation proves that this comparison is itself the pullback of
`forgetBaseYoneda g V`, so it is monic.

`FibreRestrictionAtlas` records one scheme over `T` mapping to both fibres,
a projection to `V`, the two commuting identities, and étaleness and
surjectivity of both charts. `FibreRestrictionAtlas.of_original` constructs
it from any surjective étale scheme chart of the original fibre over `S`.
The chart's second projection is represented by an actual scheme map to
`V` viewed over `S`. Compose this with `V → T` to give the same chart
scheme its structure over `T`. The identity on the underlying scheme is
an isomorphism back to the original chart over `S`.

The new chart over `T` is the actual pullback lift of the restricted first
projection and the scheme map to `V`. Its square with
`fibreRestrictionMap` and `forgetBaseYoneda` is cartesian, by cancellation
against the two proved forgetful pullback squares. Restriction preserves
the two relative scheme properties, and base change then proves that the
new chart is étale and surjective. The original chart's properties are
transported through the identity scheme isomorphism.

`FibreRestrictionAtlas.pointsHomeomorph` applies the common-atlas criterion
from `CommonAtlasPointTopology`. The transformation to the represented
`T` is the original second projection followed by `V → T`; thus it
recovers precisely the chart's new structure map. The monicity and both
atlas properties were just proved.

For a morphism of algebraic spaces, the actual algebraic-space fibre
product supplies an original surjective étale atlas. Its whole-presheaf
comparison gives an atlas of the actual presheaf pullback. This proves
`nonempty_fibreRestrictionAtlas` without extra assumptions, and choice of
such an atlas defines `fibreRestrictionPointsHomeomorph`. Its forward
function is exactly `Points.forgetBase` composed with the point map of
`fibreRestrictionMap`; the separate application lemma records this
identity.

`forgetBaseSchemePointsHomeomorph` identifies the two represented target
point spaces through their common ordinary scheme. Its function equals
the canonical forgetful point map. Naturality of `Points.forgetBase` and
the second projection identity therefore give
`fibreRestrictionPointsHomeomorph_snd`: the fibre homeomorphism commutes
with projection through this represented-target homeomorphism.

All statements retain the arbitrary universe and arbitrary scheme bases.
The provenance is internal: the module derives these constructions from
actual presheaf pullbacks, scheme Yoneda fullness, the published fibre
product construction and the proved common-atlas point-topology criterion.
It assumes no external theorem or unproved topology comparison. This
supporting unit does not prove limit descent; the full eight-property
`SpaceLimitPropertyDescentStatement` remains open.
