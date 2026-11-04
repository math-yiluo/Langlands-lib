# Effective affine descent of actual fppf quotients

`AffineFppfQuotientDescentStatement.{u}` concerns affine schemes `B` and `S`, an
fpqc morphism `p : S → B`, actual group schemes `G` and `N` over `B`, and an
inclusion `i : N → G` that is a monomorphism in schemes over `B`. Suppose an
affine group scheme `Q` over `S` is supplied with a quasi-compact fppf quotient
`q : G_S → Q` whose full kernel range equals the range of `i_S`. The statement
asserts the existence of an affine group scheme `R` over `B` and an fppf
quotient `r : G → R` with full kernel range equal to the range of `i`, together
with an actual isomorphism `R_S ≅ Q` recovering the original map `q`.
`affineFppfQuotientDescent` proves this proposition in arbitrary universe `u`.
There is no field, smoothness or reducedness assumption.

The proof is derived from the constructed quotient datum in
`Descent.FppfQuotientDatum`, the published effective affine group-scheme descent
`Descent.Datum.affineSolution`, compatible homomorphism descent, fpqc descent of
morphism properties and represented subgroup ranges. It assumes the supplied
quotient after base change; it does not assert general quotient existence.

The canonical Cech data on `G_S` and `N_S` make `i_S` compatible. The induced
quotient datum on `Q` therefore exists. Effective affine descent constructs its
solution `R`, and compatible homomorphism descent constructs `r` from `q`. The
solution's isomorphism gives the asserted recovery equation.

`RelativeRoot.IsFppfQuotient.of_baseChange_iso` proves the reflection step and
also works without affine-scheme hypotheses. Postcomposition with the supplied
isomorphism preserves and reflects flatness, surjectivity and local finite
presentation. These three properties descend along the fpqc projection from
the base-changed target, using `baseChange_map_isPullback`. On every test,
postcomposition with the target isomorphism preserves which points are killed.
Thus the full base-changed kernel of `r` is the prescribed base-changed range
of `i`. The actual kernel inclusion and `i` are monomorphisms, so fpqc reflection
of equality between represented subgroup ranges proves the original kernel
equality. Together the four conditions give the exact published
`RelativeRoot.IsFppfQuotient` predicate for `r`.
