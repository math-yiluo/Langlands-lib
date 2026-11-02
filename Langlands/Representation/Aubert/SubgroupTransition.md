# Canonical maps on the actual subgroup induction–coinvariant model

This internal construction uses actual subgroups and actual function spaces.
Its declarations lie in `Langlands.Aubert.SubgroupTransition`.
Author: Worker 194.

For an actual subgroup `P` of a topological group `G`, and `U` normalized by
`P`, `inducing P U hPU ρ` is the published unnormalized action on the
trivial-character quotient `Coinvariants ρ U 1`. `term P U hPU ρ` is its
actual smooth induced representation: covariant functions on `G` that are
fixed by one open right stabilizer for the entire function. The coefficient
ring is any commutative ring. No finite-length or reductivity premise is
used. Coefficient, group, source and target universes are independent;
induction has the existing carrier universe `max uG uV`.

For `Q ≤ P` and `U ≤ N`, where `Q` normalizes `N`, `fullMap` sends a
covariant function `f` to the function `g ↦ transitionLinear … (f g)`.
The covariance proof first uses covariance of `f` along `Q → P`, then
chooses a representative of `f g` and checks that both expressions are the
class of the same vector. Right translation commutes with this pointwise
map. `map` uses the published `smoothMap` to restrict it to smooth vectors;
`map_eval` records its pointwise formula. `map_refl` and `map_comp` follow
by evaluating functions and applying the corresponding quotient-transition
laws. Thus these are canonical maps, rather than choices of identifications
between isomorphic terms.

`termMap` is the map induced by an ambient intertwiner, using the published
localization map and smooth-induction map. `map_natural` proves the
naturality square for the canonical transitions by evaluating and invoking
the quotient naturality square.

`fullAugmentation` sends `v` to the orbit function `g ↦ [ρ(g)v]`.
Its covariance and equivariance follow from the representation
multiplication law. If `ρ` is smooth, `augmentation` uses the published
`smoothLift` to prove that these functions are smooth vectors.
`augmentation_eval`, `map_augmentation` and `augmentation_natural` prove
the evaluation formula, compatibility with transitions and naturality.

The provenance is the explicit quotient universal property, covariance
condition, right-translation action and smooth-vector restriction already
published in `Jacquet.Localization`, `Jacquet.LocalizationTransition`,
`Induction.Definitions` and `Smooth.SmoothPart.Definitions`. This is an
internal general construction. The existing GL construction
`Aubert.TransitionMaps` uses the same pointwise method; it is left unchanged.

For the Aubert application, the normalized induction of normalized Jacquet
restriction must be compared with this function model by cancelling the
actual half-modulus factors and identifying the actual Levi restriction.
That comparison, the realization of standard parabolics and radicals, and
the required containments belong to the shared general adapters. They
are not assumed as fields of a substitute group structure here. This
module alone does not construct the normalized general Aubert complex,
prove its exactness, identify its terminal homology, or establish any
support or irreducibility theorem.
