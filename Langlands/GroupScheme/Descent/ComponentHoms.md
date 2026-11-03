# Homomorphisms over finite scheme decompositions

Worker 416. This internal construction assembles actual morphisms over a
scheme from their restrictions to the finitely many components of a supplied
coproduct decomposition, and assembles actual group-scheme homomorphisms and
isomorphisms in the same way. The schemes have arbitrary universe `u`; the finite
component index is in `Type`. Reindexing any finite family by `Fin n` gives
this indexing convention without bounding the fields or schemes.

For actual maps `p i : Z i → S`, the assumption says that the actual map
`Sigma.desc p : (∐ i, Z i) → S` is an isomorphism. No decomposition of a
field tensor product is proved here. Mathlib's finitary extensivity of
schemes implies that the corresponding coproduct of pullbacks of any
`X → S` maps isomorphically onto `X`. The construction composes the inverse
of this isomorphism with the coproduct of the supplied local maps.
The projection formulas prove that the assembled morphism is over `S`,
restricts to the supplied maps, and is unique. These results package the
restriction functor as fully faithful.

For group schemes `G` and `H` over `S`, the family of pullbacks
`Over.pullback (p i)` is monoidal with the pointwise tensor structure on the
component categories. A local Cartesian monoidal instance proves that this
tensor has the required product universal property: its terminal map,
projections, pairing and uniqueness are all defined componentwise. This
instance retains Mathlib's pointwise monoidal structure.

`componentGroupHom` packages a family of actual homomorphisms
`(baseChange (p i)).obj G → (baseChange (p i)).obj H` as a homomorphism of
group objects in that pointwise category. Its unit and multiplication laws
are the supplied component homomorphisms' laws. Mathlib's
`Functor.FullyFaithful.mapGrp` then lifts it through the fully faithful
scheme restriction functor. The resulting `groupHom` is an actual
group-scheme homomorphism over `S`; `map_groupHom` proves that every
component restriction is the supplied homomorphism, and `groupHom_ext`
proves uniqueness.

The selected data-valued definition `groupRestrictionFullyFaithful`
packages these construction and uniqueness results as full faithfulness
of the actual functor
`GroupScheme S → (∀ i, GroupScheme (Z i))`. Thus every family of component
homomorphisms between two supplied global group schemes has exactly one
global homomorphism with those restrictions. `groupIso` applies `groupHom`
to the component isomorphisms and their inverses. Componentwise equality
detection proves the two inverse identities, and `map_groupIso` proves
that the restrictions are the original isomorphisms.

The intended use is the component assembly needed after a finite Galois
tensor decomposition. The construction itself assumes no
field, flatness, affineness, central isogeny, or simple connectedness.
Existence of the local lifts, the field-tensor decomposition, and effective
descent remain separate obligations. In particular this module does not
descend group objects given only on the components and does not prove the
host arbitrary-field simple-connectedness theorem.

The provenance is an internal application of Mathlib's finitary extensivity
of schemes and its fully faithful monoidal functor construction for group
objects, using the public definition of group schemes as actual group
objects in `Over S`. The decomposition is an explicit isomorphism premise,
and no field-only universal property is applied on a nonfield scheme.
