# The stabilizer of a selected geometric lift

This internal lemma uses the actual finite-etale cover category, fibre functor,
and `fundamentalGroupMap` from `FiniteEtale.Pullback`. For a cover `Y` of `S`
and a lift `x` of the point `s`, the image of the fundamental group of `Y` at
`x.left` fixes `x`. The hypotheses retain explicit finiteness of the relevant
fibres. Connectedness and algebraic closure are unnecessary.

The proof uses the identity cover of `Y.obj.left`. Every lift into this identity
cover has underlying map `x.left`, by its defining equation. The existing
`fundamentalGroupMap_smul_left_of_comp` transports this equality to the action
on `x`. This proves image containment in the stabilizer; it makes no assertion
that the image equals the stabilizer.
