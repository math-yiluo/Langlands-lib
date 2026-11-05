# Openness of relative local fibre dimension sublevels

Worker 105 proves the published proposition
`Langlands.AlgebraicGeometry.SchemeFiberGeometry.RelativeDimensionSublevelOpenness`.
The target is the openness assertion of Stacks Lemma 29.29.4, used as an
internal prerequisite toward Conrad Theorem 3.4(2).

The implemented route first identifies dimensions in actual point fibres
under an open embedding of the source, and under an injective map of the
target. The latter comparison uses equality of the two subsets of the
source; the former restricts the open embedding to the fibre. Mathlib's
canonical fibre homeomorphism identifies these subspaces with the actual
scheme-theoretic residue-field fibres.

The imported affine algebra argument constructs an open chart through
each prime with every base fibre bounded by the original local fibre
dimension. Canonical source and target global-section spectrum
isomorphisms transfer its sublevel openness to affine schemes. Finally,
at each source point, affine target and source neighbourhoods give a
restricted finite-type affine morphism. Its open sublevel has open image
in the original source and contains the chosen point. The dimension
comparison proves that image stays in the original sublevel.

The entry theorem `relativeDimensionSublevelOpenness_proof` retains
arbitrary schemes and
locally finite-type morphisms without separation or quasi-compactness
hypotheses. It does not prove retrocompactness, geometric connectedness
constructibility, or filtered descent.

The statement comes from Stacks Section 29.29, Lemma 29.29.4, tag 02FW,
registered as `stacks-fibre-constructibility-local-dimension-2026-11-04`,
SHA-256 `1f3421cf5c5733cafdf296e8a9d38af7e4730550989a3d727d4b9a61cf1f3db3`.
The dimension in both the published target and this proof is the minimum
of the dimensions of open neighbourhoods of the actual point in its
residue-field scheme fibre. It is not the dimension of the point's local
ring. The implemented proof uses the constructed polynomial charts and
actual fibre comparisons described above.
