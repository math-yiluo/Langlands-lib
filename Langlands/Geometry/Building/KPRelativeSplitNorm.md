# Relative bounded norms on direct base changes

For a compatible tower `k → L → M`, an affine commutative `k`-group scheme `T`,
and a finite Galois extension `M/L`, `relativeBoundedRationalNorm` restricts
`relativeRationalNorm` to bounded rational points of the two direct base changes
`T_M` and `T_L`. The valuations must extend one another and the upper valuation
must be invariant under `Gal(M/L)`. Boundedness is the actual common kernel of
valuations of all rational-character values.

The proof of preservation uses the actual isomorphism `towerBaseChangeIso`
between `(T_L)_M` and `T_M`. A private version records its exact commutative
base-change carriers; equality of the point maps is checked on their underlying
scheme morphisms. The existing norm compatibility then identifies the relative
norm after this point map with the ordinary rational norm of `T_L`. A general
transport lemma carries a bounded point backwards through the isomorphism,
applies boundedness of the ordinary norm, and rewrites by that compatibility.
The definition directly restricts the original relative norm, so
`relativeBoundedRationalNorm_coe` is the definitional formula on underlying
rational points.

The public `characterValuationKernelEquivOfIso` constructs the multiplicative
equivalence on character kernels induced by any group-scheme isomorphism. Its
two restrictions use character functoriality and its inverse laws use composition
of the actual group-scheme maps.

If `T_L` is split and scalar unit norms are surjective, the bounded relative
norm is surjective. A second general transport lemma first obtains a bounded
lift for the ordinary norm by `split_kernel_le_torusNormIwahori`, maps it
through the tower isomorphism, and applies norm compatibility. The resulting
point is a lift for the directly restricted relative norm. This proves
`relativeBoundedRationalNorm_surjective_of_split` without a norm-image equality
premise.

For a nonarchimedean local field `F`, set `K = UnramifiedClosure F`.
Let `E/K` be a finite intermediate field in `SeparableClosure F` and let `L/E`
be a finite Galois intermediate field in that same closure.
`relativeInertiaBoundedNorm` specializes the construction to the prescribed
spectral valuations. If `T_E` is split, its surjectivity follows from the
published scalar inertia unit-norm theorem through
`nestedIntermediate_unit_norm_surjective`; no scalar surjectivity premise
remains.

This is internal infrastructure for the nested splitting-field argument in
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Lemma 2.5.12,
printed pp.89–90 (PDF pp.120–121). It establishes bounded relative norm
surjectivity. The equality of norm images for arbitrary splitting fields and
the independence of the final zero subgroup remain separate obligations.
