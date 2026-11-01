# An affine basis for the actual small-etale transport site

This internal construction extends `EtaleTransportSite` for an actual scheme
`Y : Scheme.{u}`, a group `G : Type w`, and a genuine homomorphism
`ρ : G →* (Aut Y)ᵐᵒᵖ`. It uses Mathlib's essentially small ordinary
affine etale category `Y.AffineEtale`.

`affineBasisObject ρ` chooses the actual affine etale scheme represented by
each object of Mathlib's `SmallModel.{u} Y.AffineEtale`.
`AffineBasis ρ` equips this small object type with the category induced
from `EtaleTransport.Object ρ`. Consequently its arrows are all the
actual labelled semilinear scheme maps between the chosen affine
representatives. They are not just the ordinary maps of the small model.
`affineBasisInclusion` is fully faithful by the induced-category construction.
No smallness of `G` is needed for these constructions.

`affineBasisInclusion_isCoverDense` proves cover density. The ordinary
affine etale `Spec` functor is cover dense by Mathlib. An ordinary map
factoring through an affine object therefore belongs to an ordinary
covering sieve. The inverse unit isomorphism of the ordinary affine small-model
equivalence replaces that affine object by its chosen representative.
Including both factors with label one gives a factorization in the genuine
transport category; the isomorphism's inverse laws give the factorization
equation. The definition of transport covering and upward closure give
the asserted cover. `affineBasisTopology` is the induced topology, and
the fully faithful cover-dense inclusion is a dense subsite.

The remaining constructions explicitly assume `Small.{u} G`. The group
can still be given in an independent universe `w`; the assumption states
that its underlying type has a representative in the scheme universe.
`object_locallySmall` proves local smallness by injecting a transport
morphism into the pair consisting of its group label and underlying
scheme morphism. The scheme morphisms are already `u`-small and the
group hypothesis makes the labels `u`-small. The affine inclusion then
proves local smallness of `AffineBasis`; its object type is in `Type u`,
so the affine transport basis is essentially `u`-small.

For any coefficient category `A` with independent object and morphism
universes and limits of size `(u,u)`, the comma category used in right
Kan extension along the opposite affine inclusion is essentially
`u`-small: the affine basis is essentially small and the transport category
is locally small. Thus the needed comma-category limits exist in `A`.
Mathlib's dense-subsite comparison then proves that ordinary presheaf
restriction along the affine inclusion, restricted to sheaves, is an
equivalence. `affineBasisSheafEquiv` names its inverse equivalence from
affine-basis sheaves to all transport sheaves. Its inverse is exactly
the continuous sheaf restriction functor.

This is an internal derived construction from the actual transport site,
Mathlib's ordinary `AffineEtale` small-model and cover-density results,
its induced-category construction, and its dense-subsite comparison by
right Kan extension. No new claim is attributed to the original Harris
or Berkovich literature. This unit does not construct sheafification,
abelian structure, enough injectives, derived representations, smoothness,
supports, arithmetic towers or Harris specialization. The small-group
condition is used only in the explicitly marked smallness and comparison
section; it is not silently imposed on the earlier transport site.
