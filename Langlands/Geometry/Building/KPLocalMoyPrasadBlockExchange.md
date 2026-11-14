# Local positive-depth exchange of K-level root blocks

This internal module adapts the algebra of `MoyPrasadBlockExchange` to
maximal-unramified building data and the actual centralizer torus filtration.
It assumes only `LocalTorusCommutatorFriendly`, the exact commutator premise
of `LocalMoyPrasadPositiveProductStatement`, besides the target data.
The root-system prerequisites are proved by the integer-valued helper
modules using `exists_order_eq_one F`.

The torus-depth image normalizes every root filtration: its character
valuations vanish, equivalent valuations have the same character kernel,
and omega compatibility makes these points fix the apartment. The same
conjugation preserves both factors of the original root block. This torus
normalization proof is adapted from Worker 359’s revision-10 covariance
draft, with coauthorship.

At a fixed positive depth `r`, ordinary opposite-root exchange gives a torus
coordinate of depth `2r`, which antitonicity lowers to `r`. Doubled-positive
exchange gives depth `r/2+r` and retains the entire original positive block.
Inversion gives the other mixed exchange with the original negative block.
The doubled/doubled exchange uses ordinary exchange in direction `2a` when
that root exists; absent factors are the identity subgroup.

The published group-theoretic `twoFactorBlockExchange` combines these four
constituent inclusions using normalization by the torus-depth image. Its
output is the literal inclusion of the original positive/negative blocks
in negative block, actual torus-depth image, positive block. The proof
retains doubled-root factors in nonreduced root systems, uses the original
rational-point multiplication, and never assumes a product cover or
Moy–Prasad normality.

The final coordinate definition chooses witnesses of this literal block
exchange inclusion, recording equality in the actual rational-point group.
