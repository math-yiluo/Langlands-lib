# Equivalences of right orbit sets

This is an internal quotient helper derived from `PEL.OrbitTransport`.
It makes no independent claim about geometric monodromy or PEL pairings.

Let `G` be a group acting on the right on sets `X` and `Y`, represented by
`MulAction Gᵐᵒᵖ X` and `MulAction Gᵐᵒᵖ Y`. For a subgroup `U`, suppose
`e : X ≃ Y` satisfies `e (right x g) = right (e x) g` for all `x` and `g`.
Then `RightOrbit.equiv U e he` is an equivalence from the right `U`-orbits
of `X` to those of `Y`.

The forward map is the existing `RightOrbit.map U e he`. For the inverse,
applying injectivity of `e` shows that `e.symm` is also right-equivariant,
so it induces the inverse quotient map. The two inverse laws follow by
quotient induction from the inverse laws of `e`.

`equiv_mk` and `equiv_symm_mk` identify the maps on representatives with
`[x] ↦ [e x]` and `[y] ↦ [e.symm y]`. These formulas hold by definition.
No transitivity, freeness, topology or left action is assumed.
