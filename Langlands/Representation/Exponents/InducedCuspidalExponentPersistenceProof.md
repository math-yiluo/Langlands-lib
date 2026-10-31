# Persistence of cuspidal exponents of real-twisted inductions

Authors: Workers 99, 125 and 954.

`Langlands.glInducedCuspidalExponentPersistence.{uF,uV,uW,uM}` proves exactly
`Langlands.GLInducedCuspidalExponentPersistenceStatement.{uF,uV,uW,uM}`.
All four universes are independent. The theorem has no additional premise.
The target's Lean/Markdown pair and its imported files are unchanged.

The final theorem applies
`InducedCuspidalExponentPersistence.persistence_of_geometricLemmas` to the
published closed theorem `Geometric.padicGeometricLemma` twice: at
`.{uF,uW}` for the coarse inducing representation and at `.{uF,uV}` for
the fine inducing representation. The fine instance also supplies the
cuspidal-piece input to the published tensor reduction
`glCuspidalInductionJacquetConstituent_of_cuspidalPiece`, which discharges
the inner constituent premise. The geometric lemma and the constituent
conclusion are thus proved inputs, rather than assumptions of the final
theorem.

The supporting modules implement the following argument.

1. The coarse quotient is smooth because the actual inner induction
   surjects onto it. In the opposite Jacquet module of its twisted outer
   induction, select a geometric-filtration index containing the given
   irreducible cuspidal exponent. Proper target refinements cannot contain
   such a subquotient, by the published proper-induction vanishing theorem.
   The remaining whole-target piece is a transported refined Jacquet
   module. Retain its index, source refinement, permutation and conjugacy
   witness for every smooth inducing object in the coarse carrier universe.
2. Pull the exponent back through this conjugation and untwist by the
   negative restricted coarse parameter. The constructed flattened refined
   Jacquet twist equivalence then gives an irreducible cuspidal subquotient
   of the coarse representation's untwisted upper refined Jacquet module.
   The published inner quotient-support and upper reversal adapters,
   together with the constituent conclusion above, identify it with an
   inner block permutation of the fine representation twisted by `-v`.
3. Retwist this equivalence. Invariance of the restricted coarse character
   under the inner block permutation and composition of Levi transports
   yield the required equivalence at `t`. The output permutation is the
   outer selected permutation composed with that inner permutation.
4. At parameter zero, use the inclusion of the same selected whole
   geometric piece into the opposite Jacquet module of the untwisted
   induction. Subquotient transitivity gives occurrence of the same
   composite permutation with the same conjugacy witness. Twist and
   transport preserve the needed irreducibility and admissibility.

Clause 4 uses the actual retained filtration index; no inference from
coinciding Weyl labels or equivalent transports at `t` is needed. The proof
retains the target's arbitrary fine and coarse real parameters and arbitrary
target shape and cuspidal exponent.

This is an internal assembly of the named Library results and the three
supporting modules submitted with it. Worker 954 authored the original
opposite cuspidal-piece extraction. Worker 99 extended it to retain the
same piece for another inducing object, constructed the twist and transport
helpers, and assembled this proof. Worker 125 supplied the inner quotient
support and upper reversal adapters. The mathematical route is the
Bernstein–Zelevinsky geometric-lemma argument described in the target's
paired Markdown and used in Silberger's Proposition 6.1; this module adds
no new source-dependent definition or statement.
