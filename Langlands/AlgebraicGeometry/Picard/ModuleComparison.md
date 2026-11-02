# Actual Picard-to-module pullback comparison

`PicardGroupoid.toModuleStrongTrans F` is an internal construction for every
category `C` and functor `F : C ⥤ Schemeᵒᵖ`. Its source is the published actual
Picard pseudofunctor precomposed with `F`. Its target is the ordinary module
pseudofunctor precomposed with `F`, followed by the pseudofunctor forgetting the
right adjoint of pullback. The construction is uniform in all the universes of
`C` and in the universe of the schemes.

At `a : C`, the component is `Core.inclusion _ ⋙ LineBundle.forget _`:
it retains the actual module sheaf of a line bundle and the forward module
morphism of each actual module isomorphism. `toModuleStrongTrans_app` states this
as a reflexive equality. The naturality comparison is the identity natural
isomorphism: forgetting a pulled-back line bundle gives its ordinary module
pullback.

The proof checks the full strong-transformation laws. For identity and
composition it first computes the precomposition comparisons abstractly, including
the equality transports introduced by `F.map_id` and `F.map_comp`. Forgetting the
Picard comparisons gives precisely these module comparisons, since the published
Picard pullback comparisons were constructed from module pullback. A pointwise
constructor then checks the naturality, identity and composition laws in `Cat`.
The implementation normalizes only bundled-object, bundled-map and underlying
module projections when applying that constructor; it does not replace the
actual sheaves or their pullbacks.

The provenance is internal: this derives compatibility of the existing Picard
and module pseudofunctors by their defining constructions, rather than asserting
a new result from the literature. Specializing `F` to the opposite of
`relativeSpace f` gives the comparison on every scheme in the full slice over the
base. This module alone constructs neither a coherent-family transformation nor
an atlas, and proves no algebraicity or openness assertion.
