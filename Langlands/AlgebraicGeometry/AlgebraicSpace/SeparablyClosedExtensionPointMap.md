# Points over relatively separably closed normed extensions

Authors: Worker 114; the proof generalizes Worker 105's published completion
embedding argument.

This derived supporting construction gives a homeomorphism
`separablyClosedExtensionPointHomeomorphRange` from `X(K)` to its image in
`X_L(L)`, with the étale-chart topologies, when `L/K` is a normed extension,
`L` is henselian, `separableClosure K L = ⊥`, and `X` is quasi-separated and
locally of finite type. No separation or henselian assumption on `K` is
needed in addition to those stated. The map underlying the homeomorphism is
the previously constructed `extensionPointMap`.

The proof route generalizes the published
`HenselianCompletionPointEmbeddingProof.lean`; it does not use a new
literature assertion.

* `exists_rational_of_separablyClosed_extension` considers an `L`-point of
  an étale chart whose image agrees with the image of a `K`-point of
  another chart. The two points define a point of the represented overlap.
  Its projection is étale, and the published
  `exists_changeRing_eq_of_formallyUnramified` makes this overlap point
  rational under the relative separable-closedness assumption. Scheme
  coefficient extension is injective, so the second projection is the
  given rational point.
* `isEmbedding_extensionPointMap_of_separablyClosed` uses the covering of
  rational points by finite-type étale charts. The previous rationality
  lemma identifies every point of a base-changed chart over a rational
  image with a rational chart point. This gives injectivity. Continuity is
  the published coefficient-extension construction. For an open
  `W ⊆ X(K)`, each chart preimage extends to an open subset `t_c` of the
  extension chart. Their images are open because `L` is henselian. The
  union of these images has preimage exactly `W`, by rationality. Thus the
  source topology is induced.
* The homeomorphism is Mathlib's `IsEmbedding.toHomeomorph` for this
  embedding and has the natural coefficient-extension map as its forward
  map.

Relative separable closedness is essential to this argument. It is not
assumed in `HenselianExtensionPointEmbeddingStatement`, so this construction
is only a supporting case and does not discharge that task. No closed-image
claim is made.
