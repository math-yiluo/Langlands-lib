# Evaluation, Artin–Rees and coordinate retracts

This internal helper defines `evaluationFamily a`, simultaneous evaluation from
`Hom_B(Y,H)` to a finite product of copies of `H`. Its coordinates are the usual
linear evaluation maps. The finite index type is in universe zero, while the
rings and modules have independent arbitrary universes `u` and `v`.

If the source coaction is finitely presented over `B` and every `a i` is invariant,
`hom_eval_isHom` proves each evaluation coordinate equivariant. Tensor coordinate
extensionality from `GroupoidCoactionFinitePi` then makes `evaluationFamily`
equivariant for the actual Hom and finite-product coactions.

For finite source and target modules over a Noetherian ring,
`oneCohomologyVanishes_of_evaluation` applies the existing Artin–Rees theorem.
Its hypotheses retain an invariant ideal `I`, radical annihilator bounds on the
evaluation kernel and cokernel, vanishing for all finite coactions annihilated by
`I`, and vanishing for every ideal-power restriction of the Hom source.
Artin–Rees gives vanishing of the product coaction. A chosen index splits the
constant-family diagonal, giving vanishing of `H` by the coordinate retract.

`oneCohomologyVanishes_of_covering_evaluation` supplies the ideal-power vanishing
hypothesis using the covering Hom construction and its ideal-power descent
result. It assumes a source-cartesian equivalence with compatible target maps,
actual étale equivalence relations, an actual effective covering presentation over
its invariant ring, and faithful flatness there. Its coefficient modules lie in
`Type (max u v)`, as required by the effective descent interface. Finite
presentation of the source follows from finiteness and Noetherianity.

The kernel and cokernel bounds, invariant evaluation elements, and smaller-support
vanishing remain explicit premises. No generic-orbit geometry or support induction
is asserted here, and the host acyclicity theorem is still open.
