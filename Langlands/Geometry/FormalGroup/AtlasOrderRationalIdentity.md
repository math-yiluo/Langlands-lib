# Whole rational atlas maps under a proved identity coefficient map

This module constructs the actual integral and rational comparison
from coefficient extension by a supplied map proved equal to the identity
to the original full-order atlas. `identityAlongIso` retains the forced
coefficient-equality isomorphism followed by the actual identity-base
isomorphism. `identityAlongQuasiIsogeny` rationalizes those same integral
maps and their actual inverse equations.

`QuasiIsogeny.identityAlong_natural` eliminates the coefficient-map equality
and applies the existing identity-base naturality equation. The result is
an equation in the whole actual global rational atlas Hom, retaining both
actual rational inverse maps.

The generic global quasi-isogeny composition-unit, associativity, inverse
and cancellation laws in this module follow directly from composition in the
actual global full-order rational Hom and its stored inverse equations.
Cancellation composes with the same specified actual inverse, then uses
those global tensor laws. No inference of global tensor equality from chart
values or point evaluations is used.

Coefficient and acting rings and the rational field have separate universes,
with arbitrary finite coordinate types. Existing domain/fraction-field
hypotheses remain explicit. Covers may be infinite. Original framed identity
and composition comparisons are constructed in
`DrinfeldFramedIdentityComparison` and `DrinfeldFramedCompositionComparison`;
class functor laws and representability remain separate.
