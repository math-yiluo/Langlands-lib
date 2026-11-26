# Twisted trace regularity for a one-block shape

When `B.length = 1`, the block parabolic is all of `GL_n` and its Levi
product is isomorphic to `GL_n`. In `twistedDistribution_singleBlock`,
evaluation at the identity gives the equivalence with the Levi
representation transported along this isomorphism. Evaluation at the
identity commutes with the induced intertwiner because the entrywise
automorphism fixes the identity. Invariance of the finite-rank trace under
equivariant transport proves the equality of distributions.

`exists_oneBlock_regular_of_spectrum_split` uses two spaces `L` and `N` of
distributions. Each is stable under pullback by multiplication of tests
by invariant unramified characters. The functional agrees with evaluation
on a fixed test on `L` and kills `N`. Every irreducible twisted character
lies in `L ⊔ N`.

Transport the inducing representation from the Levi product to `GL_n` and
write its twisted character as `dL + dN` with `dL ∈ L` and `dN ∈ N`.
Twisting the inducing representation pulls both summands back by the
transported character. The functional kills the pullback of `dN` and
applies the fixed test to the pullback of `dL`. Expanding that test in
compact double cosets proves finite-evaluation regularity, and the
one-block equivalence carries the evaluations back to Levi elements.

This derived computation establishes the one-block regularity needed by
the procedure of Henniart–Lemaire II.5.13.
