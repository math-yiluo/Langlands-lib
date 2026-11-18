# Étale target descent of open immersions from morphism descent

`openImageIsoOfEtalePullbacks` equips the open image lift with an analytic
inverse. The construction assumes categorical pullbacks along étale morphisms with
étale base-change projections, as formulated by `LocalizedEtalePullbackStatement`.
It also assumes that for each pair of analytic spaces `S` and `Z`,
the presheaf of analytic maps from étale objects over `S` to `Z` is a
sheaf for `etaleTopology S`. With these two inputs, analytic open
immersions descend along jointly surjective étale target families.

The reduction uses a complete ultrametric normed field `K : Type u`,
localized spaces in universes `u, u, u`, and a cover indexed in an
arbitrary universe. Its initial open-immersion factorization lemma
allows independently chosen space and chart-index universes.

## Implemented proof

An open immersion is an isomorphism followed by the inclusion of an
open analytic domain. A map whose point image lies in its range lifts
through this inclusion by `domainLift`. Composing with the isomorphism's
inverse gives the desired analytic lift. The inclusion is a monomorphism,
which gives uniqueness.

Suppose the pullbacks of `f : X ⟶ Y` along a jointly surjective étale
family `V i ⟶ Y` are open immersions into `V i`. For any `t : T ⟶ Y`
with image in the range of `f`, pull back that cover along `t`.
The resulting maps `W i ⟶ T` are étale by the pullback premise and
jointly surjective by compatible point lifting. For any arrow
`Z ⟶ W i`, its composite to `V i` has point image in the range of the
open immersion `X ×_Y V i ⟶ V i`, by the pullback image identity.
It lifts uniquely through that open immersion. The projection to `X`
gives a lift of the resulting composite `Z ⟶ T ⟶ Y`. The categorical
pullback property identifies every other such lift with this one.

The local lifts on the `W i` therefore agree on every common
refinement in `EtaleSite T`. The Hom sheaf property glues them to a map
`T ⟶ X`. Applying separatedness to the sheaf of maps to `Y` verifies the
factorization through `f`. Local uniqueness and uniqueness of the sheaf
amalgamation give uniqueness of this factorization.

The open image domain of `f` and the map from `X` to this domain are
provided by `AnalyticOpenImmersionTargetTopology`. The domain inclusion
lifts to `X` by the factorization just proved. Uniqueness of the lift
of `f` gives one inverse identity. Monicity of the open domain inclusion
gives the other. This supplies an analytic isomorphism onto the open
image domain.

## Provenance

The proof derives the isomorphism from the localized étale site,
compatible point lifting, the open-domain factorization, and the two
explicit geometric premises. The descent step uses the representable
étale sheaf property discussed in Conrad–Temkin, *Non-archimedean
analytification of algebraic spaces*, §4.1, printed pp. 18–19.
