# Full centrality in finite coefficient models

Author: Worker 1609.

This internal proof module extends the finite coefficient descent in
`PolynomialHomFiniteDescent`. It reflects membership in the full group-scheme
center through the actual affine pullback comparison. The proof uses
`center_baseChange` and the inverse test-scheme isomorphism.

It also reflects full centrality through an arbitrary embedding of coefficient
fields. Polynomial coefficient extension is faithfully flat, so the existing
flat-surjective test-scheme reflection lemma applies. This has no finite-degree
or Galois hypothesis.

Consequently, any `FiniteGaloisHomModel` of a central vector-group homomorphism
is central. Its coefficient-extension equation identifies its extended
polynomial point with the original central polynomial point. Faithfully flat
reflection and the actual pullback comparison give centrality of the model's
universal point, and precomposition gives centrality on every scheme test.

`centralFiniteGaloisHomModel` chooses such a model together with its proof of
full centrality for an affine target locally of finite type and an algebraic
Galois coefficient extension. The degree of the original extension may be
infinite. The chosen intermediate field is finite Galois by construction.

These are derived compatibility lemmas for the central-norm route to separable
invariance of woundness. They assert no woundness equivalence themselves.
