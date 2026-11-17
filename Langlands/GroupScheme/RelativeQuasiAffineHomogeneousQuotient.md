# Smooth quasi-affine relative homogeneous quotients

This is an internal geometric consequence of the published exact-fiber quotient
construction. It constructs no new orbit map and assumes such a map as input.

Let `G` be a smooth affine group over an arbitrary scheme `S`, and let `i : H → G`
be a closed smooth subgroup. Suppose `r : G → Y` is a morphism over `S` into a
relatively affine scheme, and for every `S`-scheme `T` and every pair of
`T`-points `g,h` of `G`, equality of their images is equivalent to membership of
`g⁻¹h` in the represented subgroup `H`. Then
`exists_quasiAffine_quotient_of_map_kernel` constructs the actual homogeneous
quotient with a smooth structure morphism and quasi-affine preimages of all
affine base opens. The definition `quasiAffineQuotientOfMapKernel` chooses this
quotient together with its proved smoothness and quasi-affineness properties.

The proof retains the quotient's monomorphic embedding into `Y` using
`RelativeHomogeneousQuotientEmbedding`. The quotient has finite type over `S`
and a smooth surjective projection from `G`. Smoothness descends along this
projection by `SmoothEtaleSourceDescentProof`.

The helper `quasiAffineOver_of_mono` treats any scheme of finite type over `S`
with a monomorphism into a relatively affine scheme. The embedding is locally
of finite type because its composite with the structure morphism is, and hence
is locally quasi-finite because it is universally injective. Above an affine
base open, its target is affine and its source is quasi-compact. The separated
locally quasi-finite form of Zariski's Main Theorem in
`LocallyQuasiFiniteDescent.QuasiAffineChart` gives quasi-affineness. The imported
`HomogeneousQuotient.smooth_structure` from `HomogeneousQuotientSchemeAction`
supplies smoothness of any supplied homogeneous quotient of a smooth group.

These are derived results with provenance in the imported Library constructions
and Mathlib's Zariski Main Theorem. They do not assert the existence of exact-fiber
maps for centralizers or normalizers.
