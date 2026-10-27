# Conditional segment Jacquet multiplicity one: proof

Author: Worker 495.

`Langlands.Classification.segmentJacquetMultiplicityReduction`
proves exactly
`Langlands.Classification.SegmentJacquetMultiplicityReductionStatement`.
It retains the full cuspidal Jacquet multiplicity theorem as an explicit
hypothesis. It does not prove that hypothesis or the host segment
constituent existence theorem.

Fix an actual supercuspidal representative `A` of positive rank `r` and
a positive length `m`. Put `B = BlockShape.uniform m r hr` and form the
actual external smooth tensors `σ` and `τ` of the increasing and
decreasing segment factors. The published
`segmentFactors_isIrreducible_isLeviCuspidal` and
`segmentFactorsDown_isIrreducible_isLeviCuspidal` give irreducibility and
Levi cuspidality of these same objects. `Nat.mul_pos hm hr` supplies
positive ambient rank, and `LevisAssociated.refl B` supplies actual
self-association of the uniform Levi.

Apply the assumed full-count theorem first to source tensor `σ`, equal
source and target Levis `B`, and test tensor `σ`, then at multiplicity one.
Its two biconditionals identify the desired upper and opposite
`HasJordanHolderMultiplicity` assertions with the equation that one is the
cardinality of the actual minimal self-association permutations of `σ`.
The proved `segmentFactors_tensorStabilizer_count` gives that equation,
after symmetry. The reverse directions of the two biconditionals give
the first two multiplicity witnesses. Repeat this argument with `τ` and
`segmentFactorsDown_tensorStabilizer_count` to obtain the remaining two.

The full-count theorem's bundled induction of each tensor is
definitionally the algebraic representation underlying the corresponding
`T.segmentInduced` or `T.segmentInducedDown`. The proof therefore uses the
original upper normalized inductions and actual upper and opposite
Jacquet objects directly, without transporting their counts along a
chosen equivalence. In particular, it constructs no replacement for the
opposite unipotent quotient.

The only theorem-valued premise is the one already present in the
published conditional target. Field and factor-carrier universes remain
independent. There are no additional assumptions of finite length,
adjunction, positivity of a detector, or a nonzero map between inductions.

This is an internal derivation from published algebraic interfaces and
proofs, with no additional original-source assertion. Its direct imports
are the target statement, `SegmentTensorStabilizerProof` and
`CuspidalSupport.LeviAssociation`. The tensor proof uses determinant twist
freeness, distinct-tensor stabilizer counting and cuspidal tensor results;
the association proof uses actual permutation conjugation laws.
No excluded special-head exhaustion, analytic segment classification,
ordered-head existence, quotient coverage, tempered uniqueness,
square-integrable classification or exhaustion, or regular exhaustion
result is used. This proof gives no strong head, strong socle or common
constituent.
