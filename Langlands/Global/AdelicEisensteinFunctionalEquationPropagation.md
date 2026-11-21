# Propagation of an Eisenstein functional equation from an open patch

`Langlands.Global.eisensteinFunctionalEquation_of_openAgreement` gives
the analytic propagation step for the actual adelic Eisenstein functional
equation. The two rational Levi inclusions, the retraction of the second
one and the Weyl conjugation give the complex linear equivalence whose
forward map is the published `weylParameter`. At a fixed adelic point
the three continuation hypotheses give scalar meromorphy of the left
side, all the coefficients and the evaluations on the second parabolic's
parameter space.

The proof applies `scalarMeromorphicSumIdentity` at that point, starting
from the open patch given for the point. It obtains exactly the equality
on `DP ∩ D` at parameters whose Weyl images belong to `DQ`. Empty
coefficient families are covered by the scalar theorem.

This argument is derived from the local denominator convention of
Bernstein–Lapid §3.1. The open agreement hypothesis isolates the
automorphic comparison in the proof of Theorem 2.3 (4) in §8.6.
