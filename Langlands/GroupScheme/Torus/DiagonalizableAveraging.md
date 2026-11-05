# Translation and invariant coefficient averaging on diagonalizable groups

Worker 1552. Internal generalization of the published split-torus coefficient construction in `Rational.SplitTorusVectorExtension` to an arbitrary abelian character group `Λ`. No finite generation, torsion-free, reducedness or characteristic assumption is used. This is an intermediate construction for the linear additive extension proof, not a proof of the full extension splitting statement.

The actual group scheme is the existing `Diagonalizable.groupScheme R Λ`, represented by `R[Λ]`. Its affine points are unit-valued characters (`pointsEquiv`), and `universalPoint` is the identity of its representing spectrum. `point` extends that universal point from `R` to an arbitrary coefficient algebra `A`.

`translation r` scales the monomial indexed by `m` by `r(m)`. Its coefficient formula follows by linear induction on the group algebra. In particular, it preserves coefficient zero because every character sends zero to one. `translation_point` proves on the actual represented affine point functor that this algebra map translates the universal point by the original constant point. `translation_const` says it fixes constant points.

These are direct group-algebra and represented-functor proofs. They use no cardinality average and require no division by a group order, so they also apply to torsion groups in positive characteristic.
