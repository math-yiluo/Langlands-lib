# Linear restriction-stalk comparisons

This internal construction equips Mathlib's actual additive restriction-stalk
isomorphism with its local-ring linear structure.

For an open immersion `f : X ⟶ Y`, `restrictStalkLinearEquiv f M x`
identifies the stalk of `M.restrict f` at `x` with the stalk of `M` at
`f x`. Its coefficient ring is the original local ring at `f x`.
The action on the restricted stalk is the canonical source-local-ring action
restricted along `f.stalkMap x`.

The proof represents the image of a scalar under `f.stalkMap` and a restricted
module germ over a common neighborhood. The inverse of `f.appIso` transports
the representing section to the image open. The actual stalk map sends this
transported germ back to the chosen source germ. Its injectivity identifies the
original scalar. The two germ-scalar formulas and Mathlib's additive
restriction-stalk germ formula then prove linearity.
`restrictStalkLinearEquiv_germ` records the value on an actual germ.

`restrictStalkRankOneEquiv` transports an original stalk's linear equivalence
with its local ring to the restricted stalk over the source local ring.
`ofRestrictStalkRankOneEquiv` transports such a basis back. These constructions
compose the additive stalk equivalence, the given basis, and the ring
equivalence underlying `f.stalkMap`. Linearity follows from the comparison
above and the multiplication formula for the ring equivalence. For forward
transport, surjectivity of the ring equivalence represents each source scalar
as the image of an original scalar.

The construction uses only Mathlib's open-immersion and module-stalk interfaces.
