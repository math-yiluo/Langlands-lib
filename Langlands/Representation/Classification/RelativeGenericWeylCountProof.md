# Generic fine-twist Weyl self-association counts

Author: Worker 166.

`Langlands.glRelativeGenericWeylCount.{uF, uV}` proves exactly
`Langlands.GLRelativeGenericWeylCountStatement.{uF, uV}`. The field and
inducing-carrier universes are independent. The proof introduces no additional
hypothesis and changes no imported statement or construction.

The inputs are a positive rank, a coarse shape `B`, an actual refinement `S`,
an irreducible admissible unitarizable representation `omega` of the flattened
fine Levi `C = B.flatten S`, arbitrary fine real vector `v0`, and relatively
generic coarse vector `t`. The actual representation is the determinant twist
with exponent `-v0(k) + t(parent(k))`, exactly as in the target statement.

For each element `w` of the existing
`CuspidalSupport.AssociatingPermutations C C sigma sigma`, the third conjunct
of the published `glUnitaryWeylRealExponentRigidity` applies to its actual
underlying permutation, full-Levi conjugation proof, and transported
representation-equivalence witness. These are respectively `w.val.val.val`,
`w.val.property`, and `w.property`. The resulting membership in
`Geometric.blockWeyl B` establishes the first conjunct. The rigidity theorem
is instantiated with both carrier universes equal to `uV` for this
self-association; `uF` remains independent.

For the second conjunct, define an equivalence from the restricted subtype
to the original self-association type. Its forward map forgets the coarse
Weyl membership proof. Its inverse inserts the membership just proved for
each self-association. Both compositions are the identity by the defining
subtype operations, as verified by reflexivity in Lean. Applying
`Nat.card_congr` to this equivalence proves the required equality in the
stated direction. Both types are finite by the existing subtype instances;
there is no nonemptiness assumption or choice of representatives.

This is an internal consequence of the published rigidity theorem and the
Mathlib cardinality interface. Its provenance is the derivation explained in
[the statement](RelativeGenericWeylCountStatement.md), using
[UnitaryWeylRigidityProof](UnitaryWeylRigidityProof.md). It does not add a
separate external-source claim. No Jacquet multiplicity formula, constituent
comparison, quotient criterion, or irreducible-head conclusion is proved by
this finite-set result.

Environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`). Development compilation
is separate from exact-target validation, independent semantic review, and
Library publication.
