# The algebraic-space quotient of an étale equivalence relation

Module `Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAlgebraicSpaceQuotientProof`. It
proves the published statement
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAlgebraicSpaceQuotientStatement.{u}`, the
presentation form of Stacks Project Theorem 65.10.5 (Tag 02WW). Every étale equivalence relation
`(E.t, E.s)` over `S` has an algebraic-space quotient. Concretely, the fppf sheaf quotient of
the slice relation is an algebraic space presented by `E.U` and the quotient map.

## Statement

`etaleEquivalenceRelationAlgebraicSpaceQuotient : EtaleEquivalenceRelationAlgebraicSpaceQuotientStatement.{u}`.

## Proof

The theorem is the composite of two results.

- `etaleEquivalenceRelationAlgebraicSpaceQuotient_of` (Worker 1001, module
  `EtaleEquivalenceRelationAlgebraicSpaceQuotientReduction`) derives the statement from
  `FppfSeparatedLocallyQuasiFiniteDescentStatement.{u}`. The quotient sheaf is shown to have
  representable diagonal, using the descent statement for the kernel pair. The quotient map
  from `E.U` is then étale and surjective.
- `LocallyQuasiFiniteDescent.fppfSeparatedLocallyQuasiFiniteDescent` (Worker 1072, module
  `Descent.LocallyQuasiFiniteDescent.Proof`) proves that descent statement. It is Stacks
  Lemma 37.57.1 (Tag 02W8) in sheaf form.

The Stacks proof of 02WW uses Lemmas 65.10.3 (Tag 02WV) and 65.10.4 (Tag 0265). The proof of
Lemma 65.10.4 uses effective fppf descent of separated locally quasi-finite morphisms (Tag 02W8)
to show that the quotient has representable diagonal. The Lean route uses 02W8 in the same
place, but it works directly with the fppf sheaf quotient: there is no reduction to affine
pieces and no gluing of algebraic spaces.
