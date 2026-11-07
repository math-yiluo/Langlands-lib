# Normalized standard Jacquet lifting and rational-Levi detection

This internal adapter composes the actual normalized compact-fixed comparison
with the standard fixed-vector section and rational norm-kernel detector.
It proves neither exact VI.9.4 target and introduces no new literature assertion.
All retained structural and representation-theoretic inputs are explicit.

`Jacquet.standardNormalizedFixedJacquetLift` is a complex-linear map from the
`K ∩ M`-fixed vectors of the actual Haar-normalized standard Jacquet module of a
smooth representation `V` to `V`'s `K`-fixed vectors. It retains the explicit
`GeneralizedJacquetLemmaStatement`, the connected-reductive group, maximal split
torus, generic and local standard cocharacters, compatible split component,
pointwise `StandardParabolicBasisMember`, and compact-open `K` inputs of
`standardFixedJacquetLift`. It also assumes closedness of the actual standard
unipotent and Levi subgroups and the locally compact nonarchimedean rational-point
group instances needed for the normalized functor. Field and representation
universes are independent.

The construction applies `NormalizedJacquetBridge.normalizedFixedVectorsEquiv`
and then the chosen unnormalized `standardFixedJacquetLift`. Its map-back
identity states that composing with the actual unnormalized `fixedJacquetMap`
is exactly the fixed-vector comparison linear equivalence. The proof reassociates
linear-map composition and uses the existing unnormalized right-inverse identity.
No canonical choice of lift is asserted.

`rationalLeviJacquetFixedVectorDetection_of_surjective` adapts the existing
rational-Levi detection proof to the finiteness-free normalized bridge. It
assumes `RationalNormKernelFiniteRestrictionStatement`, the connected-reductive
ambient group and represented standard Levi, their stated topological instances,
closedness of the actual standard unipotent and Levi subgroups, and compact-open
containment of finite subsets of the unipotent subgroup. It retains compact-open
`K`, a subgroup `K0` normalizing `K`, the actual `M N K0` factorization, and
generation of `A` by its `K`-fixed vectors. For an actual subquotient `D` of `A`,
it requires explicit surjectivity of `D`'s unnormalized fixed-Jacquet map, an
irreducible actual subquotient `E` of its normalized Jacquet module, and compact
smooth dual coefficients for the restriction of `E` to the represented Levi's
intrinsic rational norm kernel. It concludes that `D` has a nonzero `K`-fixed
vector. Irreducibility is required of `E`, not of `A` or `D`.

The implemented proof transports normalized generation and the genuine
subquotient relation through `leviRationalPointHomeomorph`. Compactness of
`K ∩ M` follows from Levi closedness and compactness of `K`. The published
`rationalNormKernelFixedVectorDetection` supplies a nonzero fixed vector in `E`;
compact-open exactness lifts it into the normalized Jacquet module of `D`.
The new bridge lifts it into `D` using the explicitly supplied surjectivity.
No finite-dimensionality, admissibility, finite length, or finite generation of
`A` or `D` is assumed. Surjectivity and finite restriction are not proved by
this detector.
