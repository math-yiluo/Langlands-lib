# The sieve of full-product factorizations

This internal construction isolates locality of the generic factorization
condition used in the universal closed-factorization locus. It uses the
universal property of fiber products and descent of maps into a monomorphism
for a subcanonical topology. It asserts no existence of a representing scheme.

For arbitrary schemes over a base `S`, with structural maps `f : X → S` and
`g : Y → S`, and an arbitrary morphism `d : D → X ×_S Y`, `productMap f g t`
is the actual morphism from `X ×_S T` induced by `t : T → Y`, where the
structure map of `T` is `t ≫ g`. The sieve `sieve f g d` consists of precisely
those `t` for which this entire morphism factors through `d`. No affine,
reduced, finite type, Noetherian, or finite generation assumption occurs.

Precomposition stability is proved by constructing the induced morphism
between the relevant fiber products and composing with the supplied lift.
When `d` is a monomorphism, `isClosed` proves that this sieve is closed for
any subcanonical Grothendieck topology on schemes. A covering sieve on `T`
pulls back to a covering sieve on `X ×_S T`. Each member has a canonical
map to the product belonging to its local factorization. Composing gives
local lifts of the original product map through `d`; the imported
`FppfClosedLocusDescent.exists_lift_of_covering` glues these unique lifts.
Despite that helper's namespace, its topology parameter is arbitrary and
subcanonical. `fpqc_isClosed` specializes this argument to Mathlib's fpqc
topology. In particular no finite presentation premise is introduced.
