# Hilbert–Schmidt cuspidal operators of tensor tests in positive rank

`generalLinearTensorCuspidalHilbertSchmidt_of_pos` proves, for `0 < n`, that the cuspidal
integrated action of a tensor test `a ⊗ b` on the full almost-everywhere cuspidal subspace of
`L²` of the positive rational quotient of `GL_n` over a number field is Hilbert–Schmidt. Here `a`
is a smooth compactly supported archimedean kernel and `b` a compactly supported locally constant
function on `GL_n(𝔸_f)`, and the tensor is read on the adelic points of the group scheme `GL_n`
through `GeneralLinearGroupPoints.adelicHomeomorph`. This is the conclusion of
`GeneralLinearTensorCuspidalHilbertSchmidtStatement` for positive rank.

The proof applies `groupSchemeCuspidalConvolutionCompact` with the standard representation of
`GL_n`, a closed embedding by `generalLinearStandard_isClosedSubgroup`. Its hypothesis is
`isAdelicTestFunction_adelicTestTensor`: the tensor is an adelic test function. It is continuous
and compactly supported because the tensor is
(`CompactSmoothAdelicGLTest.continuous`, `CompactSmoothAdelicGLTest.hasCompactSupport`). Each
infinite slice is a constant multiple of the kernel `a`, read through
`GeneralLinearGroupPoints.infiniteHomeomorph`, hence plot-smooth by
`GeneralLinearGroupPoints.isPlotSmooth_iff_mem_smoothFunctions`. By
`CompactFiniteGLTest.exists_openSubgroup_biInvariant` (from
`Hecke.TestFunction.commonCompactOpenBiInvariance`) the finite factor is invariant under left and
right translation by an open subgroup of `GL_n(𝔸_f)`; its preimage under
`GeneralLinearGroupPoints.finiteHomeomorph` gives the open subgroup of finite adelic points
required on both sides (`adelicTestTensor_ofFinite_mul`).

The Hilbert–Schmidt property is the first step of the proof of Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), Theorem 9.1.2 (Lemma 9.3.3 and §9.4).
