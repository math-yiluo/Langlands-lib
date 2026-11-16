# The actual Lie determinant on parabolic families

This derived construction attaches the actual determinant of the Lie sheaf of
the chosen actual representative to each parabolic subgroup functor in every
universe. The ambient group is reductive over an arbitrary base scheme.
The presheaf takes values in `Type (u + 1)`; the line bundles live on the
actual parameter schemes in universe `u`.

The pullback comparison composes canonical smooth Lie determinant base change
with the determinant of the unique inclusion-compatible isomorphism to the
chosen representative of the restricted subgroup. The identity law follows
from its group identity law and determinant identity coherence. Composition
uses determinant base-change naturality, the actual representative composition
law and determinant base-change composition coherence. It needs no constant
rank, affine-base or splitting assumption.

`parabolicLieDeterminantPresheafLineBundle G hG` packages these line bundles
and comparisons as a `PresheafLineBundle (parabolicPresheaf G hG)`.
Its composition field is the forward pullback composition equation
precomposed with the inverse canonical line-bundle composition comparison.
The subgroup restriction composition law supplies the equality of the
restricted families.

`parabolicLieDeterminantDualPresheafLineBundle G hG` applies the generic
coherent dual construction. Its value on a family is exactly the dual of
the actual chosen representative's Lie determinant. Thus it includes the
canonical dual pullback comparison and its identity and composition laws,
rather than just an assignment of line bundles to families.

The two `RepresentativeIso` constructions compare these values with the
determinant and determinant dual of any actual representative of the same
family. They use the determinant of the unique inclusion-compatible group
isomorphism; the dual comparison applies `LineBundle.dualIso`.

All constructions and proofs here are derived from the established actual
representative, smooth Lie determinant, and coherent line-bundle dual APIs.
No further geometric theorem or outside-source translation is asserted.
This is derived infrastructure for the parabolic polarization; positivity and
global representability remain separate obligations.
