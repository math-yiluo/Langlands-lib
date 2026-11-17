# An explicit real standard-module coefficient space

This internal interface specifies coefficient maps from the published
`realStandardKFinite (r+1) ds` to complex-valued functions on `GL_(r+1)(ℝ)`.
Each map is complex-linear, intertwines the compact translations and the
actual right derivatives, and has smooth, moderate-growth values with the
specified left upper-unipotent character.

`realMatrixHeight` is the sum of the squared entry norms of a matrix and its
inverse. `realWhittakerCharacter a` evaluates `realScaledCharacter a` on
the sum of the first superdiagonal entries.

`IsRealWhittakerIntertwiner` lists these five conditions explicitly.
`realWhittakerModel` is the supremum of the ranges of all maps satisfying
them. This is an internal algebraic coefficient space. Its identification
with the Whittaker model of a continuous induced representation requires a
globalization and continuity argument; that identification is not asserted
by the definitions.

`RealLocalJacquet.dualBlock` inverts the character of a character block and
the inducing complex character of an induced block. It preserves every
block rank and therefore the rank of a presentation list. The definition
uses the existing inverse-character constructions in `ArchimedeanGamma`.

The interface is analogous to the complex-place coefficient interface used
in the sibling functional-equation development. Its provenance is internal;
it does not claim to quote a definition verbatim from the analytic literature.
