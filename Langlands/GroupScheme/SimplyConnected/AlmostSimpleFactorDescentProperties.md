# Almost-simplicity of the descended factor

This internal construction by Worker 166 proves reflection of almost-simplicity
and absolute almost-simplicity along arbitrary field extensions, then applies
reflection to the actual selected factor over its stabilizer field.

Semisimplicity reflects by the established theorem. Commutativity over the
original field would imply commutativity after extension through the all-test
pullback point equivalence. A smooth connected closed normal subgroup remains
so after extension: affineness and smoothness give geometric connectedness,
and the published subgroup base-change results give closedness and normality.
Almost-simplicity above forces its range to be trivial or full. Triviality
reflects through faithfully flat test pullbacks; fullness reflects through
fpqc descent of factorization through the actual monomorphism.

For absolute almost-simplicity, embed the original field's algebraic closure
in an algebraic closure of the extension field. The two iterated scalar
extensions agree by the standard base-change comparisons. Almost-simplicity
over the latter closure therefore reflects to the former one. This argument
does not assume algebraicity or separability of the initial extension.

The actual stabilizer-field factor recovers an almost-simple factor after the
upper field extension, so the first reflection theorem proves it almost-simple.
The definition `almostSimpleFactorStabilizerDescent` packages the same actual
affine group, closed inclusion and recovery isomorphism, together with simple
connectedness, almost-simplicity, normality and the exact inclusion equation.
It has the same arbitrary-Galois, affine and finite-presentation inputs as the
underlying stabilizer-field descent construction.

Absolute almost-simplicity also transports through actual group isomorphisms:
base-changing the isomorphism gives the corresponding isomorphism over the
algebraic closure. Thus `isAbsolutelyAlmostSimple_factorStabilizerDescent`
reflects absolute almost-simplicity of the recovered factor to this same
model. Absolute almost-simplicity of that upper factor remains a separate
input; no separably-closed-field classification result or final Weil
comparison is established here.
