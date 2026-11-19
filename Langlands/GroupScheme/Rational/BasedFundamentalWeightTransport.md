# Fundamental weights under a based root datum equivalence

Take the actual root data of two split pinnings. Suppose the simple roots
correspond under the given root datum equivalence and the coroots of each
pinning generate its integral cocharacter lattice. The two integral
fundamental-weight bases then correspond under the induced character lattice
equivalence. Evaluation on each simple coroot of the target is evaluation
on its preimage simple coroot of the source, so the Kronecker-delta pairings
identify the image with the corresponding fundamental weight.

This is an internal integral basis calculation. It combines with the
Library's `SplitPinning.isHighestWeight_restrict_iso_iff` when there is an
actual based, torus-compatible group isomorphism.
