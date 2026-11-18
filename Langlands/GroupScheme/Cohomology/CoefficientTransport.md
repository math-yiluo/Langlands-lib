# Transport through coefficient-module equivalences

For a commutative ring `R`, an actual group scheme `H` over `Spec R`, and an
`R`-linear equivalence `e : M ≃ N` between arbitrary modules,
`coefficientPointEquiv` extends `e` to the test-algebra-linear equivalence
`A ⊗[R] M ≃ A ⊗[R] N`. Tensor induction proves naturality under every test
algebra morphism; pure-tensor formulas are supplied in both directions.

`ModuleRepresentation.congr` transports a natural regular representation from
`M` to `N` by conjugating each pointwise linear action through this extended
equivalence. The group remains `H`. `congr_action` gives the intertwining
formula. Naturality follows from the original action's naturality and that of
the coefficient equivalence.

`OneCochain.congr` and `TwoCochain.congr` apply the extended equivalence to
cochain values. The final four lemmas prove that one- and two-cocycle equations
and their coboundary formulas are preserved. A one-coboundary primitive `m`
becomes `e(m)`; a natural one-cochain primitive of a two-coboundary is transported
pointwise. Applying the linear equivalence to the original equations and using
the intertwining formula proves these assertions.

This is internal derived content for the existing natural-cochain interface.
There are no flatness, finiteness, projectivity, source affineness or smoothness
assumptions. It asserts no geometric reduction-kernel comparison or vanishing
theorem.
