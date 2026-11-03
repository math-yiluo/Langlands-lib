# Affine tests detect subgroup-functor inclusions

Author: Worker 1280.

This internal construction turns inclusions checked on all affine spectrum
tests into inclusions on every original test scheme. No reducedness, finite
type, field or reductivity hypothesis is imposed.

For an affine group scheme `H` over any base scheme `S`,
`SubgroupFunctor.affineUniversalTest H` is the spectrum of `Γ(H, ⊤)`, with
structure map induced by the inverse of the canonical affine isomorphism
`H ≅ Spec Γ(H, ⊤)`. The point `affineUniversalPoint H` is that inverse.

For any group homomorphism `i : H → G`,
`range_le_of_affine_tests` proves `range i ≤ F` from the corresponding
inclusion on every test `Spec A → S`. Apply the premise to the universal
point followed by `i`; restrict back through the affine isomorphism to get
the inclusion point `i` in `F(H)`; then restrict along any lift of a point
in the range of `i`. This uses only functoriality of subgroup membership.
`le_of_isRepresentedBy_of_affine_tests` rewrites a represented source functor
as the range of its affine representative and applies this argument.
`le_of_closed_isRepresentedBy_of_affine_tests` obtains affineness of the
source from a closed embedding into an affine ambient group.

For affine `G` over `Spec R`, the Library already represents its dynamic
parabolic, centralizer and unipotent functors by affine closed subgroup
schemes. The three lemmas `Dynamic.parabolic_le_of_affine_tests`,
`Dynamic.centralizer_le_of_affine_tests` and
`Dynamic.unipotent_le_of_affine_tests` specialize the criterion to these
sources. The target `F` is an arbitrary subgroup functor and need not be
representable or a sheaf. The affine-test premise ranges over arbitrary
commutative coefficient rings and arbitrary structure maps, including
nonreduced spectra. The conclusion holds on nonaffine and nonreduced test
schemes as well.

The provenance is derived from canonical affine coordinates, subgroup-functor
naturality and the existing dynamic representability theorem. This is a
formal reduction for the dominant-combination proof; it asserts no finite
weight bound or unconditional realization by itself.
