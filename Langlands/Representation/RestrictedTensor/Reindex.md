# Reindexing the actual restricted tensor product

This internal construction reindexes the finite tensor stages and their actual
algebraic direct limit. It uses `RestrictedTensor.Basic`, the existing maps,
and Mathlib's dependent finite tensor reindexing. It makes no new
original-literature identification.

The coefficient field `K`, source and target index types, and local vector
carrier universe are independent. For an equivalence `q : ι ≃ κ`, a family of
`K`-modules `V` on `κ`, source exceptions `E`, and target reference family `e`,
the source has carriers `V (q i)` and references `e (q i)`. The target has
carriers `V j`, references `e j`, and exceptions `E.map q.toEmbedding`.
No topology, finite-dimensionality, or group action is assumed.

`reindexFinite` is the actual equivalence between each finite source set and
its image. `reindexStage` uses Mathlib's dependent tensor reindexing for this
equivalence. Its inverse pulls a tuple back along `reindexFinite`. The two
finite-stage elementary-tensor formulas state this pullback and its inverse
without identifying different dependent fibers by a definitional equality.

`reindexStage_transition` proves that this equivalence commutes with adjoining
the corresponding reference vectors. Its proof checks elementary tensors;
membership in the image finite set is equivalent to membership of the
inverse-index coordinate in the original set. Thus the two extended tuples
agree. `reindexMap` descends the compatible finite-stage maps through the
existing direct-limit universal map, and `reindexMap_of` and `reindexMap_pure`
give the exact finite-stage and elementary-tensor formulas.

Surjectivity takes a target finite representative, uses its inverse-image
finite set, and applies the inverse finite-stage equivalence. For injectivity,
the explicit hypothesis is that `e j` is nonzero outside the mapped exceptional
set. The existing injectivity of each target finite-stage inclusion then
reduces a zero image to a zero finite-stage tensor. `reindex` uses these proved
facts to construct a genuine linear equivalence. Its forward map is exactly
`reindexMap`. Nonzero references are required only for this injectivity proof
and the bundled equivalence; the map, its formulas, and surjectivity do not
require them.

This is an algebraic construction on the existing direct limits. It supplies
no group-action comparison, tensor factorization theorem, or automorphic
occurrence assertion.
