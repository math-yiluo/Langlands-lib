# Degree-zero subgroup maps

Author: Worker 45.

This file constructs subgroup restriction and corestriction on Mathlib's
actual degree-zero Tate cohomology. Restriction comes from the inclusion of
group invariants into subgroup invariants. Corestriction comes from the sum
over left cosets. The summand is defined on cosets themselves; independence
of representatives and invariance of the sum under the full group are proved.

The quotient descent certificates are proved by decomposing the group sum.
For corestriction, the full norm is the subgroup norm followed by the left
coset sum. For restriction, the full norm is the subgroup norm of the sum of
the actions of inverse left-coset representatives. Thus both maps preserve
the actual norm images. Their quotient maps are then transported along
`zeroEquiv` to actual Tate cohomology. No norm-factorization identity is
supplied as an assumption.

The subgroup need not be normal. The ring, group, and coefficient module
have arbitrary carrier universe `u`. The chosen finite enumerations of the
group, subgroup, and coset space make the finite sums available; finiteness
of the latter two follows from finiteness of the group. The quotient formula
for corestriction does not depend on a choice of coset representatives.
`Pairing.restrict` is the actual restriction of an equivariant coefficient
pairing.

The source is Serre, *Local Fields*, Greenberg translation, GTM 67 (1979),
Chapter VII, §7, p. 119 (PDF 125), and Chapter VIII, §2, pp. 129–130
(PDF 135–136). Registered source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The original pages were read. The group-sum decompositions are internal
lemmas implementing those formulas.

This pair is a definition contribution for independent review. All-degree
transfer maps, their comparison certificates, and compatibility proofs
remain separate obligations of the task.
