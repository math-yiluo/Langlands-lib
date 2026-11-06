# The actual inner action of an adjoint quotient on its source

For a supplied actual adjoint quotient `q : G → A`,
`IsAdjointQuotient.innerAction` constructs an `AutomorphicAction A G`.
The action is a morphism `A ×_K G → G` with the identity, action and group
homomorphism laws on every relative test scheme. In particular, it acts on
tests where a point of `A` has no global lift to `G`.

The proof first shows that conjugation by a point of the actual kernel of
`q` is trivial. The full scheme-theoretic centre condition in
`IsAdjointQuotient` supplies commutation with every group point on every
test and refinement. Thus the existing conjugation action of `G` on itself
satisfies `KernelActsTrivially`.

The existing `AutomorphicAction.quotientAction` construction then descends
conjugation through `q` in its acting variable. The flat and surjective
properties come from the supplied quotient. The source and target are affine
because they are connected reductive; this supplies quasi-compactness of
the quotient morphism. The generic construction performs effective
fpqc descent of the actual action morphism and proves its laws by local
lifting, without requiring smoothness of the central kernel.

`innerAction_act_lift` states the resulting all-test formula

```
innerAction(q(h),g) = h * g * h⁻¹.
```

This is an internal specialization of the published action-descent API,
with the central-kernel verification made explicit. It constructs the
adjoint quotient's action on the original group, whereas `Adjoint.Action`
constructs actions on the quotient itself. It assumes an actual adjoint
quotient and does not prove its existence, a quasi-split inner-form
existence theorem, or a cocycle-vanishing theorem. No perfectness or
characteristic restriction is imposed.
