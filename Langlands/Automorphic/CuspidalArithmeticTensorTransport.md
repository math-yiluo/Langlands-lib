# Arithmetic transport of finite cuspidal slices

The arithmetic pullback on automorphic functions identifies the finite invariant
subspaces over the two fields. Its restriction to an embedded subspace is a
linear equivalence and intertwines the finite actions via the finite adelic
group isomorphism. Every form in the pulled-back slice comes from the original
operator realization, as shown by `formInclusion_arithmeticComapEquiv`.
The order equivalence preserves the zero subspace, so the pulled-back slice
remains nonzero.

The tensor presentation uses the original factor carriers at the reindexed
places. It composes the Library's restricted tensor reindexing with the old
presentation and the equivalence onto the pulled-back slice. The exceptional
set and reference vectors follow the same place reindexing. Rebasing the tensor
equivalence uses the fact that the two finite adelic group maps are inverse.

This is an internal construction derived from `OperatorArithmeticTransport`,
`CuspidalFiniteSlice` and `FiniteAdelicGL.TensorTransport` for the proof of
`CuspidalArithmeticSpectralTransportStatement`.
