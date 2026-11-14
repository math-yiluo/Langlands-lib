# Extending a field cocharacter of a specified split torus

This internal construction supports the neighbourhood argument for relative
parabolic subgroups. Its provenance is a derivation from the Library's actual
split-torus coordinates and their arbitrary-base compatibility.

Let `T` be a commutative group scheme over an arbitrary scheme `S`, with
`IsSplitTorus T.toGrp`. For every field `k` in the same universe and every
morphism `b : Spec k → S`, the map on actual cocharacters induced by base
change is surjective.
`IsSplitTorus.extendFieldCocharacter T hT b ν` chooses an actual cocharacter
of this same `T`; `baseChange_extendFieldCocharacter` proves that its pullback
is exactly the supplied cocharacter `ν` of `T_b`.

The proof chooses a split coordinate isomorphism for `T`. It transports `ν`
to the coordinate torus over `k`, reads its integral exponent vector with
`splitTorus.cocharacterLatticeEquiv`, and uses
`splitTorus.exponentCocharacter` to realize the same vector over `S`.
The published arbitrary-base identity
`splitTorus.exponentCocharacter_baseChange` identifies its field pullback
with `ν` in these coordinates. Composing with the inverse coordinate
isomorphism gives the extension in the original specified torus.

There is no connectedness, reducedness, affine-base, characteristic or
Noetherian hypothesis. The extension is chosen and need not be unique when
the base is disconnected. The assertion concerns globally split tori;
an étale splitting cover is a separate input for applications to relative
tori.
