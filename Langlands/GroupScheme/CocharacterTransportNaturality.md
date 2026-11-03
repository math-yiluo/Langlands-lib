# Naturality of canonical descent and cocharacter transport

Worker 1270. This is an internal construction from the published scheme-pullback
composition comparison, its lift to group objects, and `CocharacterTransport`.
It provides the naturality needed when a torus cocharacter is composed with a
group homomorphism over the original base.

Let `b : S → B` and `a : S → S` satisfy `a ≫ b = b`.
The definition `descentBaseChangeNatIso` is a natural isomorphism from the
functor “pull back along `b`, then along `a`” to pullback along `b` on all group
schemes over `B`. It is the inverse of the lifted pullback-composition natural
isomorphism followed by the equality isomorphism for `a ≫ b = b`.

The theorem `descentBaseChangeNatIso_app` identifies every component with the
existing `descentBaseChangeIso`. Naturality of this natural isomorphism gives
`descentBaseChangeIso_naturality`: for every `f : H → G` over `B`, the pullback
of `f` commutes with the descent identifications. Expanding cocharacter
transport and applying that equation proves `transportCocharacter_naturality`.
Thus transporting `χ` followed by the pullback of `f` equals transporting `χ`
in the source and then following the same pullback of `f`.

The construction applies to arbitrary schemes, group schemes and homomorphisms.
The endomorphism `a` need not be invertible. It proves actual morphism equalities;
no assumption about fields, tori, representability or parabolic classification
is used.
