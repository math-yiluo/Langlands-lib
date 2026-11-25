# Outer type-A rank-one indices with fixed zero vertices

This is an internal consequence of the published actual-index
orbit, kernel-comparison and local innerness theorems. It is a restricted part
of the enumeration in `LocalRankOneTitsIndexStatement`, not its full proof.

## Construction

For any field `K : Type u`, affine locally finite-type group `G` and actual
`d : TitsIndexData G`, `d.zeroStarHom` is a homomorphism from the full group
`SeparableClosure K ≃ₐ[K] SeparableClosure K` to the permutations of
`d.zeroVertices`. It restricts the actual star action, using the published star
invariance of zero restriction. The inverse permutation uses the inverse
Galois automorphism; the inverse and multiplication laws follow from
`star_one` and `star_mul`.

`zeroStarHom_eq_one_iff` identifies its being the identity permutation with
fixing every actual zero vertex under that same Galois element.

## Outer type-A argument

`hasRankOneOuterAIndex_of_zero_star_trivial` assumes split rank one, a
numbering `e : d.Vertex ≃ Fin n` preserving every type-A Cartan entry,
nontrivial full star action, and trivial full star action on the zero
vertices. It proves the published predicate `d.HasRankOneOuterAIndex n`:
`n = 2` or `n = 3`, the distinguished vertices are exactly the two endpoints,
and the full star image under the same numbering is exactly identity and
chain reversal.

The published type-A symmetry theorem gives that exact two-permutation image.
The published rank-one orbit theorem makes the entire distinguished set the
reversal orbit of one chosen marked vertex `j`. Choose a full Galois element
acting as reversal. Every vertex not fixed by reversal must be marked:
otherwise it is a zero vertex and the assumed fixed action contradicts its
being moved. The nonidentity reversal forces `2 ≤ n`, so the endpoint numbered zero
is moved and belongs to the orbit of `j`. Thus `j` is an endpoint. If `4 ≤ n`,
vertex one is moved too, but is neither endpoint, a contradiction. Hence
`n ≤ 3`. Rewriting the marked reversal orbit as the endpoint set proves
both directions of distinguished membership in `IsNumberingOf`.

## Actual local kernels

`zeroStarHom_eq_one_of_simple_typeA_kernel` works over every
nonarchimedean local field at universe `u`, with no restriction on either
characteristic. It assumes that `G` is simply connected, `M` actually
represents the centralizer of `d`'s maximal split torus, and `D → M` is an
actual derived subgroup. It also assumes actual index data `eD` and a
`KernelComparison` along `D → M → G`, absolute almost simplicity of `D`,
and a supplied numbering of `eD` preserving every type-A Cartan entry.

The published `splitTorusCentralizerDerivedSimplyConnected` makes `D`
simply connected. `titsAnisotropicKernel` makes it anisotropic. The
unconditional published `localAnisotropicTypeAInner` then fixes every vertex
of `eD` for every full Galois element. The published
`KernelComparison.star_trivial_iff` transports this to the actual ambient
zero vertices; `zeroStarHom_eq_one_iff` gives the stated identity permutation.

`hasRankOneOuterAIndex_of_simple_typeA_kernel` combines this local theorem
with the outer type-A argument, retaining all the displayed actual kernel and
ambient-numbering hypotheses.

## Provenance and scope

All proofs are internal compositions of published results and elementary
finite-index arithmetic. The local arithmetic input is
`Langlands.GroupScheme.localAnisotropicTypeAInner` from
`SimplyConnected/LocalAnisotropicTypeAInnerProof`; its own literature
comparison is in its paired Markdown. No new original-source assertion is
introduced here, and no local classification or Kneser–Tits proof is used.

Absolute almost simplicity of the actual kernel and its type-A numbering
remain explicit assumptions. In particular, an arbitrary semisimple
anisotropic kernel can be reducible and have Galois-permuted components;
the local application does not assert triviality of that action. It also
does not construct the kernel comparison, a type-A numbering, or a
component or Weil-restriction decomposition. Inner-A marked positions,
other classical types and exceptional or trialitarian exclusions are not
treated here; the full enumeration is proved as `localRankOneTitsIndex` in
[`LocalRankOneTitsIndexProof`](LocalRankOneTitsIndexProof.md).
