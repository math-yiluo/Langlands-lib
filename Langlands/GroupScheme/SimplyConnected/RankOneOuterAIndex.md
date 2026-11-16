# The exact local rank-one outer type-A indices

This internal derivation proves
`TitsIndexData.hasRankOneOuterAIndex_of_outer_type_A`: for a simply connected,
absolutely almost-simple group over any nonarchimedean local field with split
rank one, a supplied actual type-A Cartan numbering and nontrivial full star
action imply `HasRankOneOuterAIndex n`. The conclusion includes `n = 2` or
`n = 3`, every actual Cartan entry, exactly the distinguished endpoints, and
full absolute Galois star image equal to identity and chain reversal. Every
universe and characteristic, including characteristic two, is retained.

The marking argument first works over any separable quadratic extension with
an actual `TypeAHermitianTorusCoordinates` package. Nonsingularity of the Gram
matrix gives a nonzero entry in each row. The Gram-weight pairing theorem
then supplies an opposite-weight coordinate for every cocharacter weight.
The actual positive cocharacter gives a nonincreasing coordinate-weight
sequence. A distinguished root creates a strict step; the opposite-weight
property forces its greatest coordinate weight to be strictly positive.

At split rank one there is an actual distinguished vertex. If the first
numbered root were unmarked, its actual restriction would vanish and the
first two coordinate weights would be equal and positive. Their actual
coordinate plane would be totally isotropic by the Gram-weight theorem,
forcing split rank at least two. This contradiction proves that the first
endpoint is distinguished. The published single-orbit theorem for rank one,
together with the full reversal star image, then proves that the entire
distinguished set consists exactly of the two endpoints.

For the local application, published local unitary division splitting and the
Hermitian coordinate construction supply this package on the original
quadratic star field, with no marking premise. The separately derived
anisotropic-middle Hermitian model gives the local bound `n = 2` or `n = 3`.
The exact marking and full star image combine with this bound in the stated
outer-A index predicate. `localOuterARankOneNumbering` chooses a numbering
with the proved Cartan, marking and full-star properties.

This is a composition of the published structural interfaces and the bundled
Hermitian-coordinate prerequisites, not a new claim attributed to the
literature. It imposes no triviality condition on the anisotropic kernel's
star action. It does not use downstream local classification or local
Kneser--Tits. The D and exceptional cases and the full
`LocalRankOneTitsIndexStatement` remain open.
