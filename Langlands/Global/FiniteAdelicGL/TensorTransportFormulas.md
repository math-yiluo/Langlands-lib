# Finite-stage formulas for arithmetic tensor transport

This is an internal derived construction extending
`Langlands.Global.FiniteAdelicGL.TensorTransport`. It identifies the forward map
of the existing genuine representation equivalence on canonical finite stages
and elementary tensors. It makes no new identification with original literature.

The number fields `K` and `L`, coefficient field `A`, and local model carriers
have independent universes. Write `q = finitePlaceEquiv a` for the actual
ideal-comap place equivalence from places of `L` to places of `K`. The source
factors, references and exceptional set are exactly those of
`tensorTransportEquiv`: the models are `V (q v)`, the references are `e (q v)`,
and the source exceptional set is `transportExceptional a E`. Integral fixedness
and nonvanishing of the original references outside `E` remain explicit.

`transportTensorIndex a E T` is the image `T.val.map q.toEmbedding`, regarded as
an index containing the exact original exceptional set `E`. Its containment
proof transports finite-set monotonicity along `transportExceptional_map`.
This changes only the proof of containment; its finite set is the actual image.

`tensorTransportEquiv_of` proves that applying arithmetic tensor transport to
the canonical map from stage `T` gives the canonical map from this image stage,
with the finite-stage tensor equivalence `reindexStage q T.val` applied to the
stage vector. The proof first establishes a private equality-elimination lemma
for a family of representation equivalences satisfying a given stage formula.
Eliminating the exceptional-set equality reduces that lemma to the supplied
formula. Its application to the existing transport construction reduces to the
defining finite-stage formula for `reindexMap`. Thus the theorem also accounts
for the equality elimination inside the existing arithmetic equivalence.

`tensorTransportEquiv_pure` specializes this formula using the elementary-tensor
formula for `reindexStage`. To avoid casts between dependent model fibers, its
tuple `x` is indexed by the image stage. The input tuple is its pullback along
`reindexFinite q T.val`; the output is the elementary tensor with entries `x`
at `transportTensorIndex a E T`. Only the places are reindexed; the coefficient
field and supplied vectors are unchanged. Since `reindexFinite` is an
equivalence, every tuple on the source stage admits this form.

These are formulas for the existing algebraic restricted tensor representations.
They do not assert a topology on the tensor spaces, automorphic occurrence,
factorization of an arbitrary representation, or completion of the host task.
