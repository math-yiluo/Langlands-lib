# Transporting bases along injective root-datum morphisms

This derived internal construction extends base transport to a morphism of
root data whose weight and contravariant coweight maps are both injective.
The morphism already has a bijection of all root indices and preserves every
ordered integral pairing. It need not give isomorphic full lattices, as in the
central-isogeny case.

`mapBase` sends the support of a base through the morphism's root-index
bijection. Root linear independence and positive generation push forward
through the weight map. Coroot linear independence follows by mapping a
putative relation back through the coweight map; coroot positive generation
follows by reflecting membership in the image of the generated additive
submonoid through that map's injectivity. These prove all four base fields.

`vertices` is the exact equivalence between the two simple supports. Its
underlying index map is the original morphism's root-index bijection, and
`cartan_eq` retains every ordered integer pairing. This is a general
root-datum construction; it does not by itself prove that supplied group
schemes or star actions are compatible.
