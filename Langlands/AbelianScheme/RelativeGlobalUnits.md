# Global units on relative abelian-scheme families

`UniversalGlobalFunctions A` is the explicit proposition that the actual
projection `T ×_S A → T` induces an isomorphism on global section rings for
every scheme `T` over `S`. The theorem `universalGlobalFunctions` proves it
from the published theorem `smoothProperConnectedGlobalFunctions`: each
projection is a base change of the smooth, proper, geometrically connected
structure morphism of the actual abelian scheme `A`.

For any proof of that proposition, `relativeGlobalUnitsEquiv` is the
multiplicative equivalence on units induced by the actual projection's map on
global functions. Its forward map is `relativeUnitsPullback` and its inverse
is `relativeUnitDescend`. The two inverse laws and injectivity are proved.
`relativeUnitDescend_eq_section` identifies the inverse with restriction along
the actual unit section. Thus the inverse is determined by geometry and does
not supply an arbitrary scalar or character.

`relativeUnitsPullback_map` proves compatibility with any actual map between
relative families lying over a specified parameter map, using the equality of
their composites to the parameter scheme. Injectivity and the inverse laws
then give `relativeUnitDescend_map`. The specialization
`relativeUnitDescend_naturality` covers the usual change of test scheme. The
more general formula also applies to translation maps over the parameter.

This module is an internal derived interface, built from the published
relative geometry and global-functions theorem and Mathlib's equivalence on
units induced by a ring isomorphism. It supplies the base-unit step needed
for the kernel-character construction; it makes no descent, perfectness or
duality claim. The proof of the global-functions theorem is reused rather
than repeated.
