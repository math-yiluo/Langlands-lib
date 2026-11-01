# Finite-stage formulas for genuine CM tensor presentations

This internal derived construction specializes the arithmetic finite-stage
transport formulas to the genuine finite CM tensor presentation. It supplies
formulas for the already constructed maps, with no new original-literature
identification.

The field `F` is an actual CM number field in an arbitrary universe. The local
complex module carriers have an independent universe. The input `P` is a genuine
finite tensor presentation of a specified embedded finite realization `S`; its
integral fixedness and reference nonvanishing assumptions are retained. No
nonzero condition on `S` is needed.

Write `q = finitePlaceEquiv (CMConjugation.fieldConj F)` for the actual
ideal-comap place equivalence. The transported factors, exact exceptional set,
and references are the existing `complexConjFactors`,
`complexConjExceptional`, and `e (q v)` from `FiniteTensorCMTransport`.
`complexConjTensorIndex T` is the actual image stage `T.val.map q.toEmbedding`,
viewed as an index containing the original exceptional set `E`.

`complexConjTensorEquiv_of` identifies the rebased arithmetic equivalence on
each canonical stage vector: apply `reindexStage q T.val` and then the canonical
map from `complexConjTensorIndex T` to the original restricted tensor space.
The proof directly specializes `tensorTransportEquiv_of`. Rebasing the group
action changes no underlying vector map.

`complexConjEquiv_of` follows this stage map by the original presentation
`P.equiv` and the actual function-image equivalence `S.complexConjEquiv`.
`evaluate_complexConjEquiv_of` then evaluates the original stage presentation
at `CMConjugation.adelicConj F n a`. These follow from the existing application
and evaluation identities and the proved stage formula.

`complexConjTensorEquiv_pure` specializes the arithmetic elementary-tensor
formula. Its tuple `x` is indexed by the image stage, and the source tensor
entries are its pullback along `reindexFinite q T.val`. This formulation avoids
casts between dependent local carriers and covers every tuple on the source
stage because `reindexFinite` is an equivalence. The output tensor has entries
`x` at `complexConjTensorIndex T`.

`complexConjEquiv_pure` composes this tensor identity with `P.equiv` and
`S.complexConjEquiv`. `evaluate_complexConj_pure` gives the corresponding
full adelic evaluation identity for the bundled genuine presentation
`P.complexConj`. It uses `P.equiv` on the original image-stage elementary tensor
and pulls back only the argument `a`. Complex values and tensor entries are
unchanged.

These are algebraic presentation formulas for the specified embedded space and
its actual CM image. They assert neither existence of a tensor presentation for
arbitrary form spaces nor topological tensor equivalences, spectral occurrence,
or completion of the host task.
