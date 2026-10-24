# Ordinary tensor cup connecting-map laws

Authors: Worker 45 (Lean proof and initial exposition), Worker 210 (audit and
exposition corrections).

This proof implements exactly `Langlands.Tate.OrdinaryCupBoundaryLaws`.
It is an internal derivation from the published actual ordinary cup and its
signed cochain Leibniz identity, using Mathlib's actual connecting maps.
The sign and tensor-exactness conventions agree with Serre, *Local Fields*
(1979), VIII §3, Proposition 5(iii)–(iv), printed p.131 (PDF p.137;
registered source `serre-1979-local-fields`). Serre's proposition concerns
integral Tate cohomology of finite groups. The present ordinary-cohomology
result over arbitrary commutative rings and groups is an internal derivation
from the published cochain construction, proved here using explicit lifts.

All declarations work over an arbitrary commutative ring R and group G in a
common universe u. Both laws require short exactness of the original sequence
and its indicated tensor image. There is no finiteness, scalar splitting or
additional flatness hypothesis. All natural degrees, including zero, are covered.

The helpers in `Langlands.Tate.OrdinaryCupBoundary` provide the following steps.
`cochainCup_naturality` unfolds the explicit ordered-prefix tuple formula.
The coefficient pairing compatibility moves the output map into the inputs,
and equivariance moves the second coefficient map through the prefix action.
`tensorRight_cochain` and `tensorLeft_cochain` specialize it to the actual tensor
maps, using the formula for a tensor map on pure tensors.

`delta_cocycle` applies Mathlib's `groupCohomology.δ_apply` to specified cocycles
and lifts. Extensionality of cocycle inclusions identifies Mathlib's constructed
cocycles with the given representatives. `delta_lift` obtains a lift y of a
quotient cocycle using degreewise surjectivity of the mapped cochain sequence.
The differential dy maps to zero by the chain-map equation. Degreewise exactness
then gives a preimage x in the first coefficient module. Mathlib's
`cocyclesMkOfCompEqD` proves that x is a cocycle, and `delta_cocycle` identifies
its class with the connecting image. These are lifts in the actual ordinary
cochain complexes, not assumptions about an abstract boundary operation.

`delta_degree` identifies the connecting map with an arbitrary successor target
degree with its canonical successor version followed by the displayed equality
transport. Its proof is equality elimination. Cochain transports use the
published `OrdinaryCup.transport` and its differential and composition lemmas.

For `tensor_left_boundary`, represent both cohomology inputs by cocycles and
apply `delta_lift` to the first. Cup its cochain lift with the second cocycle.
Tensor naturality shows that this cochain maps onto the quotient cup. The
published Leibniz identity reduces its differential to the cup of the first
lift's differential with the second cocycle, since the second differential is
zero. Tensor naturality identifies that differential with the image of the cup
of x and the second cocycle. Applying `delta_cocycle` to the tensor sequence
therefore gives the unsigned first boundary formula. `delta_degree` supplies
exactly the transport in the statement.

For `tensor_right_boundary`, lift the second cocycle instead. The differential
of the first cocycle cupped with its lift y is now (-1)^p times the cup with
dy, because the first differential is zero. The relation f(x) = dy identifies
this with the image of the signed cup with x. `coefficient_smul` moves the scalar through
the tensor coefficient map. Apply `delta_cocycle` with the signed cup of the
first cocycle and x as the target cocycle. The class projection preserves this
scalar. Finally multiply the resulting identity by (-1)^p and use
((-1)^p)^2 = 1 to obtain the sign on the exact side specified by the target.
The natural-degree target transport is supplied by `delta_degree`.

`ordinaryCupBoundaryLaws` packages these two lemmas without additional premises.
It proves the ordinary tensor boundary identities only; the ordinary-to-Tate cup
comparison is a separate result.
