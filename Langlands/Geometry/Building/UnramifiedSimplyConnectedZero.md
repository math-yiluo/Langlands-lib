# The unramified zero subgroup of a simply connected group

For every nonarchimedean local field `F` in universe `u`, every actual group
scheme `H` over `UnramifiedClosure F`, and every supplied
`E : UnramifiedZeroDatum F H`, this module proves
`E.zeroPoints = ⊤` when `H` is algebraically simply connected.

This is an internal consequence of the published definitions of simple
connectedness and the zero subgroup, and the proved perfectness of semisimple
groups. It is independent of the torus and finite Galois splitting field
chosen in `E`. It does not construct a zero datum or an integral model.

The proof first applies `semisimplePerfect` to identify the full range functor
of the derived inclusion `E.d` with the total subgroup functor. Comparing its
representative with the identity of `H` gives an isomorphism whose homomorphism
is `E.d`. Thus `E.D` is simply connected. Its incoming central isogeny `E.π`
from a semisimple group is an isomorphism by the defining universal property
of simple connectedness. Hence `E.π ≫ E.d` is an isomorphism. The definition
`coverIso_of_isSimplyConnected` packages this actual composite as an isomorphism
from the supplied cover `E.C` to `H`.

Applying its inverse to each rational point proves that the cover image is
the total subgroup. Finally `E.zeroPoints` is the join of this image and the
image of the torus Iwahori subgroup; a join with the total subgroup is total.
All conclusions hold at the arbitrary universe parameter `u`.
