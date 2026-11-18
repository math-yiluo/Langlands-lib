# Coefficient coherence for local quasi-isogenies and invertible sections

The results apply to formal module laws over commutative `O`-algebras `R`, `S`
and `T` and to an `O`-algebra field `F` in their universe. Coordinate types are
finite and may differ at the endpoints and across the integral comparisons.
The equations hold on arbitrary opens of `Spec R`. For local quasi-isogenies,
the input retains the nonzero image of the scalar and the divisibility
conditions of the two formal modules.

`coefficientOpenMapCompIso` compares the functor of successive inverse images
with the functor of inverse image by the composite. Its component is the
isomorphism from `coefficientOpenMap_comp_obj`. Naturality holds because
there is at most one inclusion between two opens.

`RationalSection.baseChange_transportIso` shows that coefficient pullback
commutes with transport by two integral isomorphisms. Transport composes
the section with the source inverse and the target comparison. The proof
uses preservation of section composition and of integral images to obtain
the same conjugation over the inverse-image open.

`LocalQuasiIsogeny.baseChange_idOn` shows that coefficient pullback sends the
identity local quasi-isogeny to the identity on the inverse-image open. The
identity there uses the divisibility of the pulled-back formal module.

For both `LocalQuasiIsogeny` and `RationalSectionIso`, the identity coefficient
map gives the original object after transport by the `mapIdIso` comparisons.
For two coefficient maps, pullback in succession followed by the `mapCompIso`
comparisons equals pullback along the composite, restricted along the
component of `coefficientOpenMapCompIso`. Pullback also commutes
with transport along a pair of integral isomorphisms. These equations follow
from the section equations by extensionality. For local quasi-isogenies the
other fields are propositions. For invertible sections the two-sided inverse
is determined by the forward section.

These compatibility laws are derived internally from the Library's actual
section pullback, composition and integral-isomorphism transport.
