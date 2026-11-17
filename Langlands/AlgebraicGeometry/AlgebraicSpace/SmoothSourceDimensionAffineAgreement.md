# Affine coordinates for the assembled varying-dimension analytic atlas

Author: Worker 255.

This proof implements the affine normalization transfer in
`SmoothSourceDimensionAffineAgreementStatement`, a derived part of the analytic
manifold assertion in Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), Proposition 5.4, printed pp.15–16. The
registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The auxiliary dimension and chart arguments are internal derived results,
proved from the published dimension, functoriality and manifold APIs.

The proof uses the affine coordinate diffeomorphism supplied by the admissible
pure-dimensional family. It proves that the intrinsic dimension on a pure
dimension-n space is n by comparing an actual smooth dimension-n atlas with
the published intrinsic dimension function. The inclusion of the dimension-n
piece is therefore bijective on field points. Admissibility makes this
inclusion a local analytic diffeomorphism, hence a global diffeomorphism on
points.

For each lifted chart, the coordinate map composed with its inverse is the
affine coordinate diffeomorphism composed with the piece inclusion and the
original chart inverse. Functoriality and analyticity of atlas charts prove
analyticity in every source dimension. For the reverse direction in dimension
n, the global inverse of the piece inclusion reduces the expression to the
original chart composed with analytic maps. Charts in other dimensions have
empty sources by intrinsic dimension, so their inverse-coordinate domains are
empty. Continuity in both directions follows from the original affine
coordinate diffeomorphism. The theorem is universe-polymorphic and uses only
the stated henselian field and admissibility hypotheses.
