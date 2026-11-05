# Levi-compatible Iwasawa over arbitrary real or complex coefficients

Author: Worker 1655.

This internal construction chooses a complex coefficient extension in
arbitrary universe `u` and combines the real and algebraically closed
cases. `complexLiftRCLike` transports the complex analytic structure to
`ULift` of the complex numbers through the norm-preserving downwards ring
equivalence. It retains the lifted field and induced normed structure.

The auxiliary `isAlgClosed_of_ringEquiv` generalizes the universe scope of
Mathlib's same-named algebraic-closure transfer route. Given a polynomial
in the target field, map its coefficients to the algebraically closed
source through the inverse equivalence. Degree preservation gives a root
there. Map the root back and use coefficient/evaluation compatibility to
obtain the desired target root. The existence-of-roots criterion gives
algebraic closure. The proof permits independent source and target
universes.

For a real `RCLike` field `k`, expressed by `RCLike.I = 0`, the
`realRingEquiv` identifies it with the real numbers. Compose this
identification with the real-to-complex map and the upward lift to define
`realComplexLiftAlgebra`. The scalar-tower proof checks that the image of
every original real scalar is its lifted complex image. The extension
has algebraic closure by the cross-universe transfer just established.
Every base scalar is fixed by conjugation because its imaginary part
vanishes.

`HasClosedStarRealization.hasRCLikeHermitianStarLeviRealization` now
splits on the existing `RCLike` dichotomy. If the imaginary unit is zero,
use the explicitly constructed lifted extension and the real-place
internal conjugation theorem. Otherwise its imaginary part is one, and
the existing complex ring equivalence identifies `k` with the complex
numbers. Transfer algebraic closure back to `k` and use the complex-place
internal conjugation theorem. Both cases retain the supplied common
cocharacter and its represented dynamic parabolic and centralizer.
Neither case assumes adjoint stability on an entire extension image.

Unitary diagonalization gives
`hasRCLikeDiagonalStarLeviRealization`. Under ambient affineness,
`hasRCLikeLeviCompatibleDecomposition` gives a compact with all four
actual-point conclusions: ambient maximal compactness, ordered
parabolic-image-times-compact coverage, equality of its parabolic and
Levi intersections, and maximal compactness of its inverse image in the
specified Levi point group. The point groups, homomorphisms and
regular-function evaluation topologies are unchanged. No extension
field, ring equivalence, or topology comparison is an input of these
three conditional theorems.

The provenance is internal. It composes the existing analytic
ring-equivalence transport with a cross-universe polynomial-root
argument, the explicit lifted complex extension, and the previously
proved real and complex internal conjugation constructions. Initial
ambient closed star realization and existence of the common cocharacter
for an arbitrary supplied rational pair remain prerequisites of the
unconditional archimedean theorem. This module does not prove that host
statement.
