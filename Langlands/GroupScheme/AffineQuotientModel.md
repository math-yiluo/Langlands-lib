# An affine model of a represented quotient

`AffineQuotientModel ρ` contains an actual affine group scheme with a closed
embedding into the general linear group and a group-scheme isomorphism from
the given quotient `Q`, compatible with its supplied representation `ρ`.

The constructor assumes a smooth connected affine source `G`, a finite-type
target `Q`, a flat scheme-surjective quasi-compact homomorphism `q : G → Q`,
and a representation of `Q` which is monomorphic on schemes over the base.
It applies published smooth pointed-image generation to the composite
representation of `G`. The source is geometrically integral. The resulting
smooth closed affine group `D` receives an actual homomorphism from `G`:
monomorphy of its inclusion transports the group laws to the factor.
Dominance of a positive ordered product of source images implies dominance
of this factor, because ordered multiplication factors through the source
group homomorphism.

The factor kills the full kernel of `q`, since its composite with the closed
inclusion is the original composite representation. Fpqc homomorphism descent
therefore gives `t : Q → D`. The equation `t` followed by the closed inclusion
equals `ρ` makes `t` monomorphic. The dominant factor through `q` makes `t`
dominant, hence scheme-theoretically dominant since `D` is reduced. The
arbitrary-field corollary in `DominantHomFlatProof` makes `t` an actual group-scheme
isomorphism. `AffineQuotientModel.isAffineHom` transports affineness back to `Q`.

This is an internal derived affine-model construction using actual morphisms
and all scheme tests. The faithful representation is an explicit input; no
quotient existence, unipotence, or pseudo-reductivity is asserted by this unit.
