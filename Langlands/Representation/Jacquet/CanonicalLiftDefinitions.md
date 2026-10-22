# Compressed compact actions and carriers for canonical Jacquet lifts

This module constructs normalized compact compression on actual fixed vectors,
its all-power stable-image submodule, and restrictions of the actual Jacquet
quotient. It is derived infrastructure, not a statement of a canonical-lift
isomorphism.

For a topological group G, a smooth complex representation rho on V, and a
compact open subgroup K with its compactness proof, `compressedAction rho hρ K
hK g` is the endomorphism of `fixedVectors rho K.toSubgroup` sending v to
`Compact.averageMap rho hρ K hK (rho g v)`. The codomain restriction uses the
published invariance of the average. `compressedAction_apply` exposes this
formula; `compressedAction_one` uses the average's identity on fixed vectors.
`compressedAction_natural` proves that every ambient intertwiner commutes with
compression by combining averaging naturality with equivariance. The existing
`fixedVectorsMap_id` and `fixedVectorsMap_comp` provide identity and composition
laws for the fixed-vector maps used here.

`stableImage` is exactly the submodule infimum over natural numbers r of
`LinearMap.range (compressedAction ... g ^ r)`. Its membership theorem gives a
preimage under every power, including r = 0. `powerKernelSup` is the submodule
supremum of the kernels of the same powers; no decomposition result is claimed.
`stableImageInclusion` and `stableImageToRepresentation` are the inclusions into
the fixed-vector space and then V. To construct `stableImageAction`, write a
stable-image vector as C^r w for each r. Its image is C(C^r w) = C^r(Cw), so it
remains in every power range. The evaluation and inclusion-composition lemmas
expose this restricted endomorphism.

For actual subgroups N and M satisfying `M ≤ Subgroup.normalizer N`,
`fixedJacquetMap` restricts `Jacquet.mk rho N` from the actual K-fixed vectors
to fixed vectors of `Jacquet.action rho N M hMN` under `K.comap M.subtype`.
This is the subgroup M intersect K viewed inside M. If m lies there, then
m fixes v and the quotient action satisfies m.[v] = [rho(m)v] = [v]. This proves
codomain membership intrinsically. This construction works over any
commutative coefficient ring and needs no topology. `stableImageJacquetMap`
composes its complex specialization with the stable-image inclusion. The
application and composition lemmas identify both maps with the original
quotient map. The action in both codomains is unnormalized.

The group and representation carriers have independent universe parameters,
and naturality allows an independently sized target carrier. No finite
dimensionality, admissibility, rank condition, nonzero module, proper parabolic,
or block-count restriction is imposed. Consequently zero-rank and empty or
one-block GL specializations remain admissible whenever their input data exist.

## Source and scope

Bill Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter III, revision April 29, 2019, sections 5–6, pages 5–8; especially
III.5.1–III.5.5 and III.5.7. Registered source
`casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The retained original is
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
No project errata file for this source was present when this module was written.
The source's page 7 explicitly withdraws an earlier argument over a general
Noetherian coefficient ring; the present elementary restrictions make no
admissibility or isomorphism assertion over such rings.

Casselman III.5 defines tau_a by the **unnormalized** sum over the right cosets
in K a K / K, and III.5.1 rewrites it using K / (K intersect a K a^{-1}). The
operator C here instead uses the **normalized** compact average. Equality with
tau_a is not asserted: comparison requires proving the subgroup-index scalar
factor. The source uses admissibility, a contracting element, and Iwahori
factorization to identify a sufficiently high power image and a canonical lift.
Our intersection over all power ranges and normalized compression are derived
algebraic infrastructure, not definitions literally taken from that text.

Finite-dimensional stabilization, invertibility on the stable image, splitting
by the power kernels, the index-factor comparison and the corresponding stable
images, p-adic multiplicativity, and bijectivity of the restricted quotient are
later proof obligations. No canonical pairing or opposite-duality conclusion is
included in any data field or asserted here.
