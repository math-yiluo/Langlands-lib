# Finite type systems on the actual next tuple threshold

This module is internally derived infrastructure for the descending induction
in Stacks Project, Proposition 70.8.1, Tag 07SU (registered source
`stacks-noetherian-approximation-2026-11-01`). The tuple filtration and the
cross-cover quotients have already been constructed in the Library from its
stratification sources. This module applies the stable action quotient-system
constructor to those actual constructions.

Work in arbitrary universe `u`. Let `E` have separated source, affine object
and arrow schemes, and a joint endpoint map that is a closed immersion.
Fix natural numbers `N,p` with `E.tupleLengthBound ≤ N` and `p < N+1`.
Given an affine finite type first level `M` of the higher tail
`E.tupleTailPresentation N (p+1)`,
`nonempty_finiteTypeCartesianSystem_tupleTailNext` constructs a finite type
cartesian system whose cone point is exactly
`E.tupleTailNextRelation N p`.

When `p+1 < N+1`, the acting relation is the higher tail. Its action is the
published cross-cover action on the affine cross-cover scheme, whose source
map to that tail is étale. The published finite invariant affine quotient
covers of this action and its diagonal pair action supply the two cover
inputs of `M.actionQuotientSystem`. The quotient of the first action is the
next-threshold open of the lower tail; the quotient of the pair action is
the arrow scheme of that threshold chart relation. The published threshold
comparison has identity object and arrow maps and is cartesian, so its object
map is an isomorphism. Applying the constructor to these two concrete scheme
quotients and this comparison gives the required system.

In the remaining case, `N ≤ p`. The length bound implies
`E.tupleLengthBound ≤ p+1`, so the published vanishing theorem makes the
next-threshold open empty. Its chart relation therefore has empty object
scheme. The empty-relation first-level constructor gives an affine finite
type first level of this relation, and its stable system supplies the required
system. This includes the final step `p=N` without requiring a nonexistent
chart at index `N+1`.

`tupleTailNextSystem N p hN hp M` is the noncomputable definition that chooses
a system from the proved nonemptiness result above. It has exactly the same
geometric hypotheses and bounds and returns a
`FiniteTypeCartesianSystem (E.tupleTailNextRelation N p)`. This is internal
choice packaging of the constructed system and adds no existence assumption.

The result supplies the step required by the published descending-induction
lemma. It does not itself perform that induction or assert the full Noetherian
first-level statement.
