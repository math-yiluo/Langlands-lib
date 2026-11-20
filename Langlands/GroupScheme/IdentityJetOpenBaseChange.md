# Actual identity jets under open change of base

Let `G/S` have separated structure morphism, and let `b : T → S` be an
open immersion. This internal construction compares the actual closed
identity neighborhoods and their actual module sheaves under this base change.

`identitySection_isPullback` proves that the actual identity square is
cartesian for every base change: the actual identity sections are
sections of the cartesian group structure square. For an open base
change, pullback of the identity kernel is therefore the new identity
kernel. Pullback along an open immersion commutes with ideal-sheaf
powers, as shown by `idealSheaf_comap_pow_open` on affine opens using
the actual section-ring isomorphisms of the open immersion.

`ideal_openBaseChange` identifies the actual jet ideals.
`openBaseChangeMap` is the resulting actual scheme morphism on
identity neighborhoods, with its explicit inclusion factorization.
`openBaseChange_isPullback` identifies its projection square as
cartesian by composing the closed-subscheme square with the actual
group structure square.

`openBaseChangeIso` is the isomorphism between the pullback of
`IdentityJet.module G n` and `IdentityJet.module G_T n`. It is the
existing actual open-cartesian direct-image comparison, followed by
the actual comparison from the pullback of the structure module to
the structure module. The base may be nonaffine and no smoothness,
finiteness, noetherian, or compactness assumption is imposed.
