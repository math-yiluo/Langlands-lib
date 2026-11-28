# Commutator in a normalized cocycle extension

Let \(G\) and \(A\) be commutative groups, and let \(c\) be a normalized
multiplicative two-cocycle for an action of \(G\) on \(A\). Assume that this
action fixes every element of \(A\). For any lifts \(x,z\) in `c.Extension`
with second coordinates \(g,h\), respectively,
`Langlands.NormalizedTwoCocycle.Extension.commutator_eq_inl_div` gives
\[
[x,z]=\operatorname{inl}\bigl(c(g,h)/c(h,g)\bigr),
\qquad [x,z]=xzx^{-1}z^{-1}.
\]

The lemma derives the formula from the multiplication in `CocycleExtension`.
The second coordinates of \(xz\) and \(zx\) coincide by commutativity of
\(G\). In the coefficient group, the trivial action leaves the same product
of the two first coordinates in either order. The coefficient inclusion
multiplies the first coordinate by \(c(g,h)/c(h,g)\), since the cocycle is
one on pairs with first entry one. Thus multiplying \(zx\) on the left by
this included ratio gives \(xz\). Right multiplication by \((zx)^{-1}\)
then gives the displayed commutator.
