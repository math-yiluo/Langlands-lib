# Finite permutation actions and one-stabilizer intersections

This internal construction isolates the elementary finite-action step in
Task 5976's proposed finite-vertex approximation proof. It uses the published
integer-valued building datum over any field and its actual rational-point
action on its actual reduced quotient. No local-field, topological, boundedness
or vertex hypothesis is needed for this step.

`finiteSetPermutationHom` restricts a supplied subgroup's action to a supplied
invariant finite set of building points. Its inverse at a subgroup element is
the original action of the inverse element. Thus this is the permutation
representation of the original action, with no replacement building or group.
The application lemma records its literal value on original building points.

`iInf_oneStabilizer_eq` identifies a nonempty finite intersection of
one-stabilizers with the character-valuation kernel intersected with the
pointwise fixer of that same set. Nonemptiness extracts one character-kernel
membership; fixing each point is exactly the remaining intersection condition.

`finiteSetPermutationHom_ker` assumes the supplied subgroup lies in the
character-valuation kernel. Its permutation kernel is then exactly the
intersection of the finite family's one-stabilizers, restricted to that
subgroup using `subgroupOf`. The proof evaluates the equality of permutations
at each actual point in one direction, and proves equality pointwise in the
other. This equality also holds for an empty finite set.

`normal_finiteIndex_iInf_oneStabilizer` rewrites by that kernel equality.
Normality is normality of a group-homomorphism kernel; finite index follows
because the permutation group of a finite set is finite. This proves the
group-theoretic conclusion once an invariant finite set is supplied. It does
not prove that the unrestricted intersection is contained in the supplied
subgroup: without that additional fact, `subgroupOf` is its intersection with
the subgroup.

The provenance is elementary composition of the original building action,
the published definitions of one-stabilizers and pointwise fixers, and
Mathlib's finite-kernel-index theorem. This is not a new literature assertion.
For the unramified-model application, constructing an appropriate nonempty
finite set of actual vertices, proving its invariance under the required
norm-one fixer, and proving containment of the vertex-fixer intersection
remain geometric obligations. No integral-model existence, maximal boundedness,
or neutral-component point comparison is proved here.
