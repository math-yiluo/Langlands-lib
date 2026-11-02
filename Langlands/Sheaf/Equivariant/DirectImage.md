# Direct image along a continuous equivariant map

This module constructs direct images of full ordinary-open equivariant
sheaves along an actual continuous equivariant map. It also constructs
precomposition on every locally constant coefficient section, natural in all
original coefficient intertwiners and compatible with identities and
composition. The wider Harris implementation remains incomplete.

## Provenance and parameters

This is internal derived infrastructure. It combines the existing
`ActionOpens`, `TopologicalSheaf` and `LocallyConstantSheaf` constructions with
Mathlib's topological sheaf direct image. It makes no new translation claim
about an original-literature theorem. The imported construction
`TopCat.Sheaf.pushforward_sheaf_of_sheaf` proves the ordinary sheaf condition
for inverse images of opens; this module retains all group-labelled arrows
while applying that result. The import `Mathlib.Topology.Sheaves.Functors` is
from the project's pinned Mathlib.

The group `G : Type v` has a group structure. The spaces `X`, `Y` and, for
composition, `Z` lie in a common universe `u`; each has a topology and a
`G`-action. The input is an actual continuous map `f : C(X,Y)` with a proof
`hf : ∀ g x, f (g • x) = g • f x`. The general construction requires no
topology on `G` and no continuity assumption on the actions. The coefficient
category `A : Type a` has morphisms in independent universe `b` and need not
be complete or cocomplete.

The coefficient section additionally assumes `ContinuousConstSMul G X` and
`ContinuousConstSMul G Y`, and the corresponding assumption on `Z` for
composition. These hypotheses ensure that the existing labelled point maps
are continuous. The commutative ring `R : Type r` and module carrier
`M : Type w` have independent universes. There is no topology on coefficients,
finite-dimensionality, local compactness, total disconnectedness, separation
or stable-neighbourhood assumption. Full coefficient sheaves take values in
`ModuleCat.{max u w} R` and coefficients vary through `Rep.{w} R G`.

## Inverse images and full transport presheaves

`preimage f hf` is the functor from `ActionOpens G Y` to `ActionOpens G X`
sending an open `U` to the actual inverse image `f⁻¹(U)`. An arrow labelled
`g` retains exactly that label: if `g • U` is contained in `V`, equivariance
of `f` proves that `g • f⁻¹(U)` is contained in `f⁻¹(V)`. Identity and
composition laws use equality of the unchanged labels. `preimage_mem` and
`preimage_map_label` expose the original inverse image and label formulas.

`presheaf f hf A` is precomposition by the opposite of this functor. Thus
its value on an open `U` is the original module or object of sections on
`f⁻¹(U)`, and every labelled restriction is the original presheaf map for
the corresponding inverse-image arrow. Morphisms are whiskered original
natural transformations. `underlyingIso` identifies the composite with
forgetting labels with ordinary topological presheaf direct image. The
isomorphism is reflexive because these functors agree definitionally.

## Sheaves and comparisons

`isSheaf` applies Mathlib's direct-image sheaf theorem to the actual underlying
ordinary sheaf. `sheaf f hf A` lifts the entire transport-presheaf direct
image to the existing full category `TopologicalSheaf G Y A`. No section
submodule, selected open cover or additional morphism condition is used.
The lemmas `sheaf_obj_obj`, `sheaf_obj_map` and `sheaf_map_app` are reflexive
identities for every open, labelled arrow and original sheaf morphism.

`toSheafIso` identifies forgetting equivariance after direct image with
ordinary sheaf direct image after forgetting equivariance. `idIso` identifies
direct image along the identity with the identity functor. For an actual
continuous equivariant `g : C(Y,Z)`, `compIso` has endpoints

`sheaf (g.comp f) ... A ≅ sheaf f hf A ⋙ sheaf g hg A`.

The composite's equivariance proof rewrites `hf` and `hg`. All these
isomorphisms are `Iso.refl`: they retain the original objects and morphisms
and exploit definitional equality of inverse-image precomposition and
proof irrelevance for the intrinsic proofs.

## Locally constant coefficients and original maps

For each target open `U`, `pointMap f hf U` is the continuous restriction

`f⁻¹(U) → U`, sending `x` to `f(x)`.

`coefficientMap f hf ρ` is a morphism from the full locally constant sheaf
on `Y` for `ρ` to the direct image of the full locally constant sheaf on
`X` for the same `ρ`. At `U` it is the actual linear precomposition map
`s ↦ s ∘ pointMap f hf U`. `coefficientMap_apply` gives this formula for
every section and every point of the inverse-image open. It retains the
entire locally constant section module.

Naturality applies to every labelled arrow `k : V → U`, including
non-inclusion transport arrows. The existing sheaf pullback applies the
original coefficient operator `ρ(k.label⁻¹)`. The two composites therefore
apply the same coefficient operator to section values at the points
`k.label • f(x)` and `f(k.label • x)`, respectively. Subtype extensionality
and `hf` identify those points. Module-map, linear-map and locally constant
function extensionality prove the resulting equality of full section maps.

`coefficientNatTrans` assembles these sheaf morphisms into a natural
transformation

`LocallyConstantSheaf.functor R G Y ⟶
 LocallyConstantSheaf.functor R G X ⋙ sheaf f hf (ModuleCat R)`.

For every original coefficient intertwiner `c`, both composites send `s` at
`x` to `c(s(f(x)))`; the proof is pointwise reflexivity.
`coefficientMap_id` gives the identity sheaf morphism for the identity map.
`coefficientMap_comp` proves that the morphism for `g.comp f` is the morphism
for `g` followed by the direct image along `g` of the morphism for `f`.
The target sheaves agree definitionally, as in `compIso`; both sides
evaluate to `s(g(f(x)))`.

## Retained boundaries

These constructions use ordinary topological opens and actual equivariant
continuous maps. No general smoothness-preservation assertion for direct
image is made. No inverse-image adjunction, compact-support functor,
supported Godement or derived comparison, analytic or etale identification,
arithmetic tower or Harris specialization is supplied here. Variation along
the actual rational-spectrum maps is a subsequent specialization. The
coefficient precomposition map is a morphism; it is not asserted to be an
isomorphism for an arbitrary continuous equivariant map.
