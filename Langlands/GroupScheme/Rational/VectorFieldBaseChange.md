# The standard vector group under actual field extension

Worker 1317. This is internal support for scalar extension of the supplied
Steinberg root maps. It is derived from the existing natural-vector-coordinate
comparison, actual pullback point equivalences, affine Lie-kernel coordinate
formulas and actual field extension of tangent points. It has no external
source claim.

`RelativeRoot.kernelFieldExtension_vectorLiePoint` works for any group scheme
with supplied natural vector coordinates. Extending the coefficients of its
actual dual-number identity-kernel point sends epsilon coordinates `x_j` to
`algebraMap k F x_j` in the pulled-back coordinate model. The proof cancels the
actual Lie-kernel base-change equivalence, applies affine vector coordinates,
uses their compatibility with base change and coefficient maps, and compares
the two components of each dual number. No affineness is needed for this
kernel-point identity.

For every dimension, `VectorGroup.fieldBaseChangeIso` is an actual group-scheme
isomorphism from the actual pullback of the standard polynomial vector group to
the standard vector group over the extension field. It is constructed from the
existing `RelativeRoot.vectorGroupIso` using the actual pulled-back natural
coordinates. `coordinates_fieldBaseChangeIso_hom` states equality of its global
vector coordinates on every scheme test; `affineCoordinates_fieldBaseChangeIso_hom`
gives the corresponding coefficient-algebra coordinates.

`targetMap_fieldBaseChangeIso_vectorLiePoint` consequently shows that this actual
isomorphism sends each dual-number identity-kernel vector to the standard vector
with the same epsilon coordinates. Applying the preceding coefficient-extension
identity and the published pure-tensor Lie scalar-extension formula gives
`targetMapLinear_fieldBaseChangeIso_standardEpsilon`: the actual differential
of the comparison sends `Lie.schemeScalarExtension (1 ⊗ standardEpsilon k)` to
`standardEpsilon F` exactly. Affineness is taken from the standard polynomial
models and their pullbacks; local finite type follows from smoothness of the
standard vector group.

The fields lie in the same arbitrary universe, and the extension is arbitrary.
There is no algebraicity, perfectness, characteristic, infinitude or algebraic
closedness restriction. The module does not construct a transported normalized
root family or compare ordered Steinberg products; these are the consumers for
which the coordinate and epsilon identities provide the source normalization.
