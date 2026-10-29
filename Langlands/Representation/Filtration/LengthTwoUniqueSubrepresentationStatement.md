# Unique nonzero proper subrepresentation from a length-two count

Author: Worker 163.

`Langlands.LengthTwoUniqueSubrepresentationCriterion` is an internal derived
statement for the algebraic step of the two-supercuspidal product argument.
It asserts no proof and does not by itself establish a result about parabolic
induction or Jacquet modules.

## Data and hypotheses

Let `k` be a field, `G` a topological group and `A` an actual smooth
`k`-representation of `G`. The target `σ` is an arbitrary representation of
the same group over the same field, on a carrier in an independent universe.
No topology or smoothness is required of `σ`.

There is a natural-number count `μ` on the actual invariant subspaces of `A`,
strictly increasing under strict containment, with `μ 0 = 0` and `μ A ≤ 2`.
Let `f : A → σ` be an actual nonzero intertwining linear map. Assume `A` is
not irreducible and every invariant subspace of count one is contained in
`ker f`. These are explicit mathematical premises. In particular, the
annihilation premise is additional information; a length bound alone does
not imply uniqueness.

## Conclusion

The proposition asserts all three of the following:

1. `A` has an actual composition series of length two, expressed by
   `HasCompositionSeriesLength A.obj 2`.
2. There is exactly one invariant subspace different from both `⊥` and `⊤`.
   Uniqueness is equality in `Subrepresentation A.representation`.
3. For every such subspace `S`, both the actual smooth representation on `S`
   and the actual smooth quotient `A / S` are irreducible.

The representations and quotients are the published `SmoothRep` constructions,
not abstractly chosen subobjects or quotients. Irreducibility includes
nonzeroness. The four universes of the coefficient field, group, source carrier
and target carrier are independent. There are no finite-dimensionality or
finite-length assumptions beyond the stated count conditions.

## Derived provenance and intended use

This is our own algebraic formulation of part of the count argument in
Bernstein--Zelevinsky (1977), §2.16(1), printed pages 449--450 (PDF pages
10--11). In that argument, the count comes from §2.14, and Frobenius reciprocity
supplies an annihilation property. The source is registered as
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The arbitrary-field and topological-group version here is derived, not a
quotation of BZ77.

The algebraic reason these premises suffice is that every nonzero proper
subspace has count one. Reducibility and the nonzero map give at least one
such subspace, so the kernel is nonzero and proper. Every nonzero proper
subspace lies in that kernel; equal counts prevent strict containment.
Consecutive inclusions in `0 ⊂ S ⊂ A` are covering pairs, making both actual
factors irreducible and supplying the two-step composition series.

The published `LengthTwoFactorMatchingCriterion` compares composition factors
of two representations; it does not expose this actual subspace uniqueness
or the actual smooth subrepresentation and quotient conclusions. This
criterion is intended to fill that small algebraic gap. Any application to
two-supercuspidal induction must still prove reducibility, construct the
strict count and nonzero map, and discharge the annihilation premise. It
must also independently prove any asserted Jacquet-module equivalences.
The present statement imports no classification, segment, derivative or
square-integrability result.
