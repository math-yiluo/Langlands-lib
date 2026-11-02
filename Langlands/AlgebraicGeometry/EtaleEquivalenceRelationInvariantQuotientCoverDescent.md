# Finite invariant covers with affine quotients descend to one level

Author: Worker 706.

This internal construction descends a supplied finite invariant affine cover
of the limit of a cofiltered cartesian diagram of étale equivalence relations.
If each chart relation in that cover has an affine quotient, the same holds
for all the descended charts at one common level. The construction retains the
indexing type, the covering property, affineness, invariance, and the exact
inverse images in the limit. It also transports the resulting data along every
transition into that level.

The diagram is `D : I ⥤ EtaleEquivalenceRelation.{u}`, with `I : Type u` and
`Category.{u} I`. Its morphisms are the actual cartesian relation morphisms
defined in `EtaleEquivalenceRelationCartesianDiagram`. The cone `c` is supplied,
and only its object-scheme cone is assumed limiting. For the cover descent,
`I` is cofiltered and both the object and relation schemes of every level are
affine. The limit is not assumed Noetherian or of finite type. The finite
indexing type `K : Type u` may be empty.

The application is the finite-cover argument of Stacks Lemma 70.5.11,
[Tag 07SR](https://stacks.math.columbia.edu/tag/07SR), after the affine descent
step of Lemma 70.5.10,
[Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ), and before the scheme
gluing used in Proposition 70.8.1,
[Tag 07SU](https://stacks.math.columbia.edu/tag/07SU). The registered originals
are `stacks-stratification-2026-11-02` (`07SR.html`, full finite-cover proof)
and `stacks-noetherian-approximation-2026-11-01` (`07SQ.html`, eventual
cartesian-comparison step, and `07SU.html`, descent of the schemes `W_i`).
The category formulation and the explicit open-chart diagrams below are
derived presentation-level constructions. They do not assert either full
algebraic-space lemma. Scheme gluing and the final Noetherian first-level
construction remain separate steps.

`CartesianMorphism.ext_of_objMap` proves that equality of the object maps
determines the whole morphism. The two endpoint equations of a cartesian
morphism and the target relation's monomorphism property determine the
relation map. This is used to verify functor and cone identities for the
restricted charts.

`IsCartesianHom.hasAffineQuotient_open_preimage` starts with a cartesian
morphism from `E` to `F`, both with affine object schemes, and an affine open
`V` of `F.U` whose chart relation has an affine quotient. The induced map
between the chart over `f ⁻¹ᵁ V` and the chart over `V` is cartesian by
`isCartesianHom_invariantOpenMap`. The inverse image is affine because `f`
is a morphism between affine schemes. The proved cartesian affine-quotient
theorem then gives an affine quotient for that inverse-image chart. No
invariance hypothesis on `V` is required for this lemma.

The next declarations are in `CartesianDiagram.OpenChart`. Initially they
use a natural transformation `t : D ⋙ objectFunctor ⟶ const S` and an
arbitrary open `V` of `S`, without affineness assumptions.

`opens` is the actual inverse-image open `t.app i ⁻¹ᵁ V`.
`preimage_opens` proves its compatibility with transitions from naturality
and inverse-image functoriality. `objMap` restricts the original object map
using `Scheme.Hom.resLE`; `objMap_ι` gives its equation with the open
inclusions. `isPullback_objMap` proves the corresponding square cartesian
by the open-immersion pullback criterion and the inverse-image equation.

`map` uses `Chart.hom` for its relation map and `Chart.isCartesianHom` for
cartesianness. `diagram` assembles these actual chart relations and maps.
Its identity and composition laws follow by cancelling the open inclusion
on object maps and then using `ext_of_objMap`. `inclusion` is the natural
transformation of object diagrams with components the open inclusions.

Given `p : c.pt.U ⟶ S` and equations
`(c.π.app i).objMap ≫ t.app i = p`, `preimage_opens_cone` identifies each
cone-leg inverse image with `p ⁻¹ᵁ V`. `coneObjMap` is the restricted
object cone leg, `coneObjMap_ι` gives its inclusion equation, and
`isPullback_coneObjMap` proves its open-immersion square cartesian.
`coneMap` equips the restricted object leg with its actual chart relation
map and cartesianness. `cone` assembles the chart of `c.pt` over
`p ⁻¹ᵁ V` into a cone over `diagram`, checking naturality by cancellation
of the open inclusion and naturality of the original cone.

`isLimitObject` assumes cofilteredness and that the original object cone
is limiting. Cofilteredness supplies connectedness.
`isLimitOfIsPullbackOfIsConnected` applied to `inclusion` and the proved
cone-leg pullback squares makes the restricted object cone limiting.
This step requires no affine schemes.

For the remaining `OpenChart` declarations, `S` and all level object
schemes are affine. `isAffine_object` pulls back the affine open `V`
along `t.app i`. With all level relation schemes also affine,
`isAffine_relation` applies `Chart.isAffine_arrows` to the resulting
affine chart object. `exists_hasAffineQuotient` assumes the preceding
object-limit hypotheses and an affine quotient for the restricted limit
chart. It applies the generic `CartesianDiagram.exists_hasAffineQuotient`
to `diagram` and `cone`, using these affine instances and `isLimitObject`.
`hasAffineQuotient_of_map` transports an affine quotient along a transition
of the open-chart diagram using the proved cartesian affine-quotient
theorem. This last lemma needs no affineness of the level relation schemes.

The final declarations are in `CartesianDiagram`, with cofiltered `I`,
affine objects and relations at all levels, and the supplied limiting
object cone.

`exists_invariantAffineQuotientCover` first applies the earlier
`invariantAffineCoverModel` to descend the given finite invariant affine
cover, retaining its exact limit inverse images. Let `i` be that model's
index. Restrict `D` to `Over i`, so each object has its actual map to `i`
and the restricted object cone is still limiting. For each cover member,
form the inverse-image chart diagram over its open at `i`. Its limit
chart has the supplied affine quotient by the model's inverse-image
equation. `OpenChart.exists_hasAffineQuotient` therefore supplies an
index `j_k : Over i` with an affine quotient for that chart.

`IsCofiltered.wideCospan` applied to the finite family of arrows
`j_k.hom` gives one common index `l`, an arrow `l ⟶ i`, and arrows
`l ⟶ j_k.left` compatible with these maps to `i`. Pull the original
model cover back to `l`. Inverse images preserve its covering,
affineness and invariance, and the cone equations retain all prescribed
limit opens. The compatible arrows define morphisms in `Over i`, so
`OpenChart.hasAffineQuotient_of_map` gives an affine quotient for every
chart at `l`. The proof also works for empty `K`; no extra inhabitedness
assumption is introduced.

`InvariantAffineQuotientCoverModel` extends `InvariantAffineCoverModel`
by the affine-quotient property of every chart at its recorded index.
`invariantAffineQuotientCoverModel` chooses such a structure from the
proved existence theorem. `InvariantAffineQuotientCoverModel.pullback`
accepts any actual arrow `j ⟶ M.index` and constructs the same type of
model at `j`. Covering and invariance follow by inverse image,
affineness by the affine transition map, and the original limit
inverse-image equations by cone naturality. The open-preimage quotient
lemma supplies its chart quotients. The pullback definition itself
requires neither cofilteredness, the limit proof, nor finiteness of `K`;
its data and the supplied arrow suffice.

All choices in this module are choices of proved witnesses. The mathematical
inputs are the imported invariant-cover and generic affine-quotient descent
proofs, actual chart pullbacks, connected-limit preservation, and
cofilteredness. No approximation statement is used as an assumption.
