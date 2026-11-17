# Source automorphisms acting freely on closed embeddings

Given an actual `ClosedEmbeddingModel H G`, each isomorphism of `H` induces
an automorphism of the parameter scheme by precomposition of its universal
family. Evaluation at every scheme-valued point identifies this parameter
map with precomposition of the corresponding embedding. Successive parameter
maps reverse the order of the source isomorphisms. The action maps preserve
the given base scheme.

More generally, a group `K` indexing source automorphisms in that reversed
composition order gives a `FiniteFreeSchemeAction` on the parameter scheme,
provided its source maps remain injectively indexed after base change to
**every nonempty test scheme**. The constructor does not require `K` finite;
the quotient constructions impose that assumption when used.

This is derived internal content. The full universal property classifies
the precomposed universal family. Pullback compatibility proves its
all-test evaluation formula and the identity and composition laws. The
inverse source isomorphism supplies the inverse parameter map. To prove
freeness, equality after an arbitrary test-valued embedding gives equality
of the base-changed source maps by cancellation of the closed embedding.
The explicit faithful-indexing hypothesis then identifies the two group
elements. The construction asserts no automatic faithfulness for a supplied
source action; that hypothesis must be proved in each application.

The module also classifies the conjugation family of any supplied closed
embedding by an actual map from `G` into the embedding scheme. Its evaluation
at every test-valued group point is exactly the conjugation family. Closedness
follows from base change of the original embedding and composition with the
actual inner automorphism.
