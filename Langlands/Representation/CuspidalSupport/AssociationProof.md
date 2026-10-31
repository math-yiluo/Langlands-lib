# The association equivalences for cuspidal Levi induction

Authors: Worker 72 and Worker 120 (logical assembly).

`Langlands.CuspidalSupport.cuspidalInductionAssociation` proves the published
`CuspidalInductionAssociationTheorem.{uF,uV,uW}` from
`NormalizedCuspidalInductionStatement`. It quantifies every prime, every
actual finite p-adic field extension, every compatible topological
realization, and every natural rank, including zero. The field universe and
the two inducing carrier universes are independent.

For any two block shapes and irreducible smooth Levi-cuspidal inducing
representations, it proves all three equivalences: their association is
equivalent to a nonzero intertwiner between their canonical normalized
inductions, to matching actual Jordan–Hölder factors with multiplicity,
and to a common actual irreducible subquotient. Association retains the
actual permutation conjugacy of the embedded Levis and inverse-conjugation
transport. Induction retains the canonical positive half-modulus twist
and smooth right-translation function space.

Factor matching is witnessed by actual finite composition series, a
permutation of their indices, and representation equivalences between the
corresponding graded quotients. A common subquotient is witnessed by
invariant subspaces, their actual quotients, irreducibility, and an actual
representation equivalence across the two carrier universes. The theorem
adds no theorem-valued, positivity or finite-dimensionality hypothesis.

## Implemented proof

The closing theorem applies `AssociationAssembly.allRanks`, whose complete
logical argument is explained in the paired `AssociationAssembly.md`.
It supplies every input with a published proof:

- `associatedCuspidalInductionHomTheorem` supplies forward Hom at both
  `{uF,uV,uW}` and `{uF,uV,uV}`.
- `representationAssociationReflexivity` supplies reflexive association
  for the source inducing data.
- `associatedCuspidalInductionFactorsTheorem` supplies matching actual
  factors for arbitrary block counts at positive rank.
- `cuspidalInductionLength.{uF,uW} F T m` supplies finite group-algebra
  module length of the target induction, from which the assembly extracts
  its Artinianness.
- `cuspidalInductionReverseAssociation.{uF,uV,uW} p F T m` supplies the
  implication from a common actual irreducible subquotient to association.
  Its target is the existing `CuspidalInductionReverseAssociationTheorem`,
  used directly by the assembly.

At positive rank, diagonal forward Hom and reflexivity first prove that
the source induction is nontrivial. Target Artinianness then allows
`nonzeroHomCommonSubquotient` to produce a common irreducible subquotient
from a nonzero intertwiner. Source nontriviality allows
`sameFactorsCommonSubquotient` to produce one from matching factors.
The reverse association theorem proves the converse implications.
Forward Hom followed by its bridge proves the remaining forward
common-subquotient implication. These deductions, together with forward
factor matching, give all three equivalences.

The rank-zero branch is the published
`cuspidalInductionAssociationRankZero`, reached by the exhaustive split
`Nat.eq_zero_or_pos`. Thus the positive-rank premises of the two forward
theorems impose no restriction on the closing theorem's rank.

## Provenance and scope

This is an internal deduction assembling published proofs of the existing
target. The source is Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), Theorem 2.9(a), printed page 448/PDF page 9.
The reverse implication follows their Jacquet descent route in sections
2.13–2.15, printed page 449/PDF page 10, through the published reverse
proof. Forward factor matching follows the elementary-map and adjacent
block reduction in sections 2.16–2.17, printed pages 449–450/PDF pages 10–11,
through the published forward factor proof. Registered source:
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Rank zero is the internal extension already proved in the rank-zero module.

The original statement pair and all imported published pairs are unchanged.
The conditional helpers in `AssociationAssembly` have their inputs fully
discharged here. The closing theorem assumes no association equivalence or
other unproved proposition.
