# Associated sheaf maps across equivariant covers

Author: Worker 13.

This internal construction extends the published `Associated` invariant-sheaf
construction to maps between different cover objects and different deck groups.
Its provenance is categorical: restriction of sections along products, the
naturality of sheaf morphisms, and the proved universal property of the invariant
limit. It does not transcribe an external theorem. The implementation uses the
published `productSheaf`, `diagonal`, `associated`, `inclusion`, `lift` and
`hom_ext`, together with Mathlib's `Action.res` for restriction of group actions.

## Inputs and variance

Let `C` be a category with binary products and Grothendieck topology `J`, and
let `R` be a commutative ring. The coefficient ring, module carriers and groups
`G`, `H`, and, for composition, `K`, share universe `u`. The site object and
morphism universes `w` and `v` remain independent. The groups have no topology
and need not be finite. For constant coefficients the construction additionally
uses `HasSheafify J (ModuleCat R)`.

The inputs are actions `Y : Action C G`, `Z : Action C H`, a homomorphism
`φ : H →* G`, and an equivariant map

`a : Z ⟶ (Action.res C φ).obj Y`.

Thus `Z.ρ h ≫ a.hom = a.hom ≫ Y.ρ (φ h)`. For coefficient sheaf actions
`F` of `G` and `E` of `H`, the coefficient map is

`c : (Action.res (Sheaf J (ModuleCat R)) φ).obj F ⟶ E`.

Its equation is `F.ρ (φ h) ≫ c.hom = c.hom ≫ E.ρ h`. The construction returns

`crossCoverMap J φ a c : associated J Y F ⟶ associated J Z E`.

In particular, the direction in the cover is contravariant and the direction
in coefficients is covariant. Neither the group homomorphism nor the cover map
is required to be surjective.

## Construction and certificates

`coverPullback J a F` restricts sections along `a × id`: its component at `U`
is the actual sheaf restriction `F.obj.map (prod.map a (id U)).op`.
Product functoriality proves naturality in `U`, the identity law and the
contravariant composition law. Naturality in `F` is the naturality equation
of the coefficient sheaf morphism. `coverPullback_deck` transports the cover
equivariance equation through this restriction.

`crossCover_diagonal` combines that deck equation, naturality of restriction,
and the coefficient equivariance equation. It proves that the composite
of `coverPullback` with `productSheaf.map c.hom` intertwines the diagonal action
of `φ h` on the source with that of `h` on the target. The diagonal action is
the existing inverse-deck convention from `Associated`.

The invariant inclusion on the source, followed by that composite, is therefore
invariant under every element of `H`. Applying the existing universal `lift`
defines `crossCoverMap`. `crossCoverMap_inclusion` computes it after the invariant
inclusion in the target, so the construction supplies an actual sheaf morphism
rather than assuming a comparison map.

`crossCoverMap_id` proves the identity law. `crossCoverMap_sameCover` identifies
the construction for an identity cover map and group homomorphism with the
existing `associatedFunctor.map`. For a second homomorphism `ψ : K →* H`, cover
map `b : W → Z|K`, and coefficient map `d : E|K → D`, `crossCoverMap_comp` states
that composing the two associated-sheaf maps is the map for `φ.comp ψ`, cover
map `b ≫ (Action.res C ψ).map a`, and coefficient map
`(Action.res (Sheaf J (ModuleCat R)) ψ).map c ≫ d`. The proof compares both maps
after the invariant inclusion, uses product restriction functoriality, and
moves the coefficient map past restriction by its naturality.

`associatedCoverChange` assembles the maps with identity coefficient morphisms
into a natural transformation from `associatedFunctor J Y` to group restriction
followed by `associatedFunctor J Z`. Its naturality is proved by the same
inclusion equation and naturality of restriction. `constantCrossCoverMap`
applies the actual constant-sheaf functor to coefficient representations and
maps, then uses `crossCoverMap`; its identity and composition certificates are
inherited from the general construction.

## Scope

These constructions require neither a covering condition nor a torsor condition.
They assert no invertibility, local triviality, exactness, or commutation of
coefficient reduction with invariants. A map from a deeper cover to a coarser
cover induces the associated-sheaf map towards the deeper cover. To construct
inverse coefficient transitions between sheaves from varying covers, one still
needs a justified torsor comparison isomorphism to reverse the cover comparison
after coefficient reduction. Geometric base change to a different site, that
torsor comparison, and actual Harris level schemes and finite etale torsors
remain separate obligations.
