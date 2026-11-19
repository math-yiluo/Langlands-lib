# Shifted Weyl translates of regular parameters leave the leading chamber

`Langlands.Global.EisensteinAmbientWeylSeparationStatement` uses a
compatible root presentation `r` of a parabolic in a connected
reductive group. Fix a finite set `S` of shifts in its ambient real
character space. There is a threshold `R` such that for every
`R`-regular complex parameter and every nonidentity relative Weyl
element `w` sending all selected Levi simple roots to positive
roots, the following pairing is negative for some ambient simple
root. Restrict the real part of the parameter to the split
component, take its orthogonal lift to the ambient torus, apply
`w`, and add a shift in `S`. Pair the result with the simple root
using the ambient Weyl-invariant form. The threshold works for
all choices of `w` and of the shift.

This is derived from the Weyl separation argument of
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein
series*, Lemma 6.8. Their lemma gives a negative pairing along a
simple root of the relevant target parabolic. The formulation here
detects exclusion from the ambient leading chamber of §6.2 by an
ambient simple root. It uses the invariant form and the regularity
predicate of `AdelicEisensteinConvergenceStatement`, with the
finite shifts representing the bounded exponent offsets used in
Proposition 6.9 and §8.6. The formulation is algebraic and works
over an arbitrary field.
