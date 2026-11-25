# Descending a commutative quotient through an inner twist

Suppose the local isomorphisms from `G` to `H` over an fpqc cover have overlap
relation given by conjugation by the cocycle `ζ`. For a homomorphism `q` from
`G` to a commutative group `Q`, the composite of each inverse local isomorphism
with `q` is independent of the cover point. Conjugation vanishes on the
commutative target. `LocalGroupIso.descendInnerQuotient` descends this natural
family and its local value formula follows from `LocalGroupHom.comp_value`.

Over the cover the resulting map to `Q` agrees with `q` after precomposition with
the recovered group isomorphism. This identity descends smoothness and
surjectivity of the original map. Pasting the defining pullback square of its
kernel with the isomorphism square identifies the two actual kernels over the
cover. For a field extension, preservation and reflection of simple
connectedness transfer it from the original kernel to the descended kernel.

This construction supplies the quotient and its kernel for the inner twisting
step in Milne, *Algebraic Groups* (2017), Theorem 25.71, printed p. 565
(`milne-2017-algebraic-groups`).
