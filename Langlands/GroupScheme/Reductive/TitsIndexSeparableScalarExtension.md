# Actual Tits-index Cartan and star comparison over separable intermediate fields

This is derived comparison material for actual semisimple groups
over arbitrary fields and at every universe parameter. It imports the actual
Galois-pinning scalar-extension construction, the existing change-of-splitting-
field comparison, Tits-index existence, semisimple field extension, and
star-action independence.

For an intermediate field `E` of the ground field's separable closure and a
supplied `E`-algebra equivalence from `SeparableClosure E` to the ground field's
separable closure, `SeparableScalarExtension` contains an actual Tits index of
`G_E`, an equivalence of all simple vertices, preservation of every ordered
integral Cartan entry, and compatibility with every absolute Galois element
over `E`. The corresponding ground-field Galois element is obtained by
conjugating through the supplied closure equivalence and restricting the
resulting automorphism's scalars to the ground field.

`nonempty_separableScalarExtension` constructs this data. First use
`GaloisPinningData.rootDatumScalarExtension` to retain the original splitting field while
changing the ground field to `E`. That pinning's torus is a torus over `E`, so
it splits over `SeparableClosure E`. The existing `exists_stage` comparison
then gives Galois pinning data over this closure and a full based root-datum
equivalence intertwining compatible automorphisms through the supplied closure
map. Semisimple field extension and Tits-index existence give an actual Tits
index of `G_E`. Star-action independence compares its pinning with the just
constructed pinning.

Compose the first root equivalence, the inverse splitting-field comparison,
and the last independence equivalence. Their support comparisons give the
full vertex equivalence, and the composite root-datum equivalence's pairing
law gives every ordered Cartan equality. For star compatibility, closure
conjugation makes the automorphisms compatible. Apply the three full star
intertwining equalities to one root index, compose the resulting equalities,
and cancel the inverse vertex equivalences. The same Galois element works on
all simple vertices.

`separableScalarExtension` chooses one such comparison. No finite-dimensional
hypothesis on `E` is required in this module. It does not compare distinguished
or zero-restriction vertices, since these can change under scalar extension.
It does not choose an almost-simple factor, identify factor roots with a
Cartan component, or claim component-factor existence. Those structural
comparisons remain separate. No downstream local classification or
Kneser–Tits input is used.
