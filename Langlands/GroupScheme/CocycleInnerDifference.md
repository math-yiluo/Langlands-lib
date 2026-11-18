# Comparing cocycles by inner twisting

Worker 838.

Let `ξ` and `ζ` be two natural cocycles of `G` on the same cover. Suppose a
group scheme `H` is equipped with local identifications `e` from `G` whose
overlap discrepancy is conjugation by `ζ`. `Cocycle.innerDifference` is an
actual cocycle of `H` with value `e_a(ξ(a,b) ζ(a,b)⁻¹)`. When multiplying
two consecutive values, the overlap relation moves the second local
identification to the first and introduces the conjugation by `ζ(a,b)`.
The two original cocycle identities then give the required product.

`Cocycle.isTrivial_innerDifference_iff` identifies trivializations of this
difference with twist cochains between `ξ` and `ζ`. The witness is
transported through the local identification at the identity point of the
cover, and naturality transports its values on each test. The base-change
lemma derives local triviality from a local twist cochain through the
published pullback point equivalence. If two homomorphisms agree under the
local identifications, `Cocycle.map_innerDifference_toFun` computes the
image as the pointwise difference of the two original images.

This is an internal all-test formulation of the twisting argument used
in Milne, *Algebraic Groups* (2017), Theorem 25.71, printed p. 565
(`milne-2017-algebraic-groups`).
