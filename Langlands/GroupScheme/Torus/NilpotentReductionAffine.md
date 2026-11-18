# Affineness and diagonalizability from a nilpotent reduction

This internal reduction is derived from the published finite-surjective affine
descent theorem and the published nilpotent diagonalizable deformation theorem.
For a scheme over an affine ring, its projection from a nilpotent scalar
reduction is a surjective closed immersion, hence finite. If the reduction is
affine, finite-surjective affine descent makes the original scheme affine.
In particular, a group with multiplicative-type reduction is affine, and the
published flat affine split reflection theorem then applies without an initial
affineness hypothesis on the group. No finite-presentation hypothesis is used.

The data-valued `affinePresentation` returns the canonical isomorphism from the
original scheme to the spectrum of its global sections, after establishing its
affineness by this argument. The other declarations implement the two group
scheme consequences above. The split consequence retains the same finitely
generated character group by the imported deformation theorem.
