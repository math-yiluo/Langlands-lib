# Rigidified line bundles and their pullback

For a scheme morphism `ε : S ⟶ X`, `RigidifiedLineBundle ε` is the full
subcategory of `RigidifiedModule ε` whose underlying module sheaf is locally
free of rank one. An object is therefore an actual line bundle `L` with an
isomorphism `O_S ≅ ε* L`. Its morphisms are actual module morphisms preserving
this isomorphism, as in the imported rigidified-module category.

`ofLineBundle` equips a line bundle with a given rigidification.
`forgetToRigidified` forgets local rank one, while the faithful functor `forget`
forgets rigidification. `trivial` uses the structure sheaf with the inverse
of the constructed canonical `pullbackUnitIso ε` as rigidification.
`isoMk` constructs compatible isomorphisms, and `transport` and `transportIso`
transport both the rigidification and the local rank-one property along an
actual isomorphism of the underlying modules.

Given a commuting square `ε' ≫ f = g ≫ ε`, the functor
`RigidifiedModule.pullback f g comm` specializes the previously constructed
`pullbackWithUnit` using `(pullbackUnitIso g).symm`. Thus no unit isomorphism
is an extra input. Its rigidification is the composite
`O_S' ≅ g* O_S ≅ g* ε* L ≅ ε'* f* L`.
`RigidifiedLineBundle.pullback` restricts this functor using the proved
preservation of local rank one. The forgetting comparison records agreement
with the ordinary line-bundle pullback. Functor laws for fixed `f` and `g`
are inherited from module pullback and the full-subcategory construction.

For `f : X ⟶ S` with an actual section `ε`, `relative f ε section_eq T`
uses the induced section on `T ×_S X`. The functor `relativePullback h` for
`h : T ⟶ U` is constructed by applying the preceding commuting-square
pullback to the naturality square of `relativeSection`.
The factor order agrees with `RelativeGeometry`; its canonical symmetry
identifies it with the source's `X ×_S T`.

This is derived infrastructure for Edixhoven–van der Geer–Moonen,
*Abelian Varieties*, Chapter VI §1, paragraph (6.2), printed page 88
(PDF page 92). The source defines rigidifications and compatible morphisms
there and gives pullback along morphisms of `S`-schemes. The extension here
to arbitrary commuting squares follows the same pullback comparison and
does not use the extra hypotheses in condition (*). Those hypotheses are
used for subsequent statements about automorphisms and Picard functors,
which this file does not assert.

The local rank-one interpretation is the one in the imported `LineBundle`
module; its equivalence with tensor-invertibility remains separate.
This file does not construct tensor products of rigidified objects,
isomorphism-class groups, identity/composition comparisons between the
rigidified pullback functors, a Picard presheaf, or a Poincaré bundle.

Registered source: `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
SHA-256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`,
Chapter VI §1, (6.2), printed page 88.
