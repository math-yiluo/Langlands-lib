# Quasi-separated finitely presented quotients of scheme relations

Author: Worker 116.

This internal construction strengthens the published étale scheme-relation
quotient by retaining the finite presentation and quasi-separatedness needed
for `SpaceLimitModelExistenceQuasiSeparated`.

For an étale equivalence relation over an affine scheme base with affine
object scheme, locally finitely presented structure map and quasi-compact
relation structure map, `quotient` chooses the published algebraic-space
quotient and its actual atlas and represented kernel pair.

The intrinsic quasi-separatedness argument checks the diagonal on the
product of the atlas with itself. The relative product morphism is étale
and surjective by base change and composition. Its pullback of the diagonal
is the relation's comparison map to the product of the object scheme with
itself, which is quasi-compact. Quasi-compactness descends along the
étale surjection by the published relative-property descent theorem.
The original structure map of the affine object scheme supplies the
quasi-compact locally finitely presented atlas of the quotient.

The private descent instance first proves that quasi-compactness descends
along a surjective quasi-compact scheme morphism: the compact preimage upstairs
maps surjectively onto the required preimage downstairs. Mathlib then passes
from fpqc descent to fppf descent for a property local on the target. The
private product lemmas express a product of two morphisms as two base
changes. The public `FinitePresentationRelationQuotient.isPullback_kernel_diagonal`
identifies a represented kernel pair with the corresponding base change of
the diagonal; it is also reused by `ReducedClosedSubspaceProof`.

This is the quotient step of the existence argument in the proof of Stacks
Project Lemma 70.7.1 (Tag 07SK). Registered source
`stacks-limit-morphism-review-2026-11-07`, directory SHA-256
`35f3718ed86ff158e3a8f3765940bd0a8e69861a3af500daf315ec210efe1663`,
file `07SK.html`, paragraph forming the quotient of the descended relation.

The construction does not descend a relation to a finite stage and does not
yet identify its change of base with a given space.
