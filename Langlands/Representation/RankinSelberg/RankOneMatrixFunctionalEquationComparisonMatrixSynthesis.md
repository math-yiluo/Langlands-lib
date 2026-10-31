# Compact character synthesis on full matrices

This internal helper transfers compact character synthesis on the actual general
linear group to Schwartz–Bruhat tests on the full matrix space. It works over
any Hausdorff topological field with continuous inversion and for every matrix
size, including zero. It is a prerequisite for the matrix comparison; it does
not prove a Fourier identity or weighted extraction.

`groupTestToMatrixTest r` is a complex linear map from Schwartz tests on `GL_r(K)`
to Schwartz tests on `M_r(K)`. It uses the published open embedding
`isOpenEmbedding_generalLinear_val` and the corresponding homeomorphism onto its
range. Pullback along the inverse homeomorphism gives a test on that open
subspace, and the published `SchwartzBruhat.extendZero` extends it to the whole
matrix space. Compact support in the subspace ensures that this extension
remains locally constant at the boundary.

`groupTestToMatrixTest_apply` proves that its value at the actual matrix of a
group element is the original test value.
`groupTestToMatrixTest_eq_zero` proves vanishing at every singular matrix.
`tsupport_groupTestToMatrixTest_subset` strengthens this to containment of the
ambient topological support in the invertible locus; this follows from compact
support and the published zero-extension support theorem.

`exists_matrix_characterOrbitIntegral_eq` takes a closed subgroup `H` of the
actual `GL_r(K)`, its Borel measurable structure, a supplied Haar measure that is
also right invariant, and a continuous character `chi : H -> C^units`. The
ambient group must have the literal compact-open neighborhood basis stated in
the theorem. For every member `f` of the published space
`Induction.CompactFunctions H (characterRepresentation chi)`, it constructs one
full-matrix test `Phi` such that for every actual group element `g`,

    integral_H chi(h)^(-1) * Phi((h*g).val) dmuH(h) = eval f g.

The theorem includes `Integrable` for this exact complex integrand at every `g`.
The measure, character and function are the supplied ones; no normalization or
unitarity hypothesis is added. Compact support modulo `H` is the compact
induction condition and does not assert compact support on the group itself.
The theorem requires no second-countability hypothesis.

The implemented proof first applies
`CompactWhittakerSynthesis.exists_characterOrbitIntegral_eq` to obtain an actual
group test, then uses `groupTestToMatrixTest`. Pointwise agreement on group
matrices transfers both the integral identity and the integrability proved by
`characterOrbitIntegrable`. This is an internal derivation from the published
GL open embedding, test-function pullback and zero extension, and the compact
character synthesis helper, with no external mathematical assertion used.
