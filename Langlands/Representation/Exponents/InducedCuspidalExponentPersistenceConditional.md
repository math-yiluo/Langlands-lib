# Conditional persistence assembly

This module reduces the unchanged four-universe
`GLInducedCuspidalExponentPersistenceStatement` to geometric-lemma instances
at the independent fine and coarse carrier universes. The underlying theorem
`persistence_of_geometricLemma_of_constituent` first proves the implication
from `PadicGeometricLemmaTheorem` and
`GLCuspidalInductionJacquetConstituentStatement`; the final wrapper derives
the latter premise from the fine geometric-lemma instance. No closed
geometric-lemma proof is constructed here. The final module
`InducedCuspidalExponentPersistenceProof` applies the wrapper to the published
`Langlands.Geometric.padicGeometricLemma` at both carrier universes.

The proof first derives smoothness of the coarse quotient from its actual inner
induction surjection. It selects a whole-target piece of the geometric
filtration for the given twisted constituent and retains that same filtration
index for every other smooth coarse inducing representation.

It pulls the constituent back along the selected whole-Levi conjugation,
untwists by the negative restricted coarse parameter, and moves the actual
subquotient across the constructed refined Jacquet twist equivalence. The
result is an irreducible cuspidal upper-Jacquet subquotient at parameter zero.
Worker 125's upper quotient-support adapter, conditional on the exact
constituent proposition, identifies it with transport of the fine representation
twisted by `-v`. Its conjugating permutation lies in the coarse block Weyl group.

The restricted coarse real twist commutes with this inner permutation.
Retwisting the identified representation and composing with the selected outer
permutation gives the required equivalence at parameter `t`. At parameter zero,
the same whole geometric piece is a subquotient of the entire opposite Jacquet
module. Actual subquotient transitivity and transport give occurrence of the
same composite permutation and conjugacy witness. Irreducibility and
admissibility follow from the published twist and transport laws.

The construction is internal: it composes the actual quotient equivalences,
actual subquotient laws and geometric extraction developed for this task.
Worker 99 authored this assembly and the persistent-piece extraction; Worker
125 authored the inner quotient and upper reversal adapters. The original
geometric extraction was authored by Worker 954.

`persistence_of_geometricLemmas` composes this assembly with the published
`Langlands.glCuspidalInductionJacquetConstituent_of_cuspidalPiece` and Worker
954's `glInducedOppositeJacquetCuspidalPiece_of_padicGeometricLemma`.
The latter supplies the cuspidal-piece statement at universes
`.{uF,uM,uV}` from `PadicGeometricLemmaTheorem.{uF,uV}`. The published tensor
reduction then gives precisely the constituent premise at `.{uF,uV,uM}`.
Together with `PadicGeometricLemmaTheorem.{uF,uW}` for the coarse inducing
representation, this proves the same persistence proposition at all four
independent universes.

Thus the wrapper does not require a separate proof of the constituent statement
once the geometric lemma is available at both carrier universes. Its provenance
is direct composition of the named actual-piece extraction and published tensor
reduction, with no change to the persistence target.
