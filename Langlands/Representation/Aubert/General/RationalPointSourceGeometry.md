# Point-Coxeter source geometry from standard-face pairings

Worker 1186, with Worker 1493's orbit and standard-face shift arguments and
Worker 181's point root-support proof.
This internal construction derives the three actual point-source intersection
identities from the root-length and positive-simple-reflection comparisons
retained in the rational Jacquet target. It works over any field in universe
`u`, for the actual point Weyl quotient and the literal simple relative roots.
It does not require a scheme Coxeter realization.

## The root condition

`PointSourcePairingFaces i ν hN hZ cs` is a proposition. For finite simple-root
labels `I,J`, every minimum representative `w` of `W_I w W_J`, every
cocharacter `zeta` standard for `rootSet i ν I`, and every simple root `a` in
`J`, it requires

- `⟨w a, zeta⟩ ≥ 0`;
- `⟨w a, zeta⟩ = 0` if and only if
  `a ∈ simpleImage cs w⁻¹ I ∩ J`.

The action here is the published `weylCharacterAction`, with the actual point
normalizer and centralizer comparisons `hN,hZ`. This predicate contains no
subgroup identity or representation comparison.

`pointSourcePairingFaces_of_rootComparisons` proves this condition from
`RootLengthComparison` and `PositiveSimpleReflectionComparison`.
The imported
`point_pairing_weyl_nonneg_of_mem_closure` gives nonnegativity for the simple
generator `a`. The imported
`point_mem_intersectionSubset_iff_pairing_eq_zero` identifies zero transported
pairing, for `a ∈ J`, with membership in the intrinsic intersection subset.
The published `intersectionSubset_eq_simpleImage_inter` identifies that subset
with `simpleImage cs w⁻¹ I ∩ J`. Simplifying finite-intersection membership
reconciles the finite-set equality instances.

## Restricted dynamic comparison

`pointSourceComparison_of_pairingFaces` assumes the root condition and the
published `StandardCocharacterStatement`, along with connected reductivity,
maximal splitness, genericity of `ν`, affineness, monicity of the torus inclusion,
and a finite enumeration of the simple roots. For every specified `w` and
normalizer lift `n`, put `K = simpleImage cs w⁻¹ I ∩ J`. It constructs a
cocharacter `eta` standard for `rootSet i ν K` such that, on every point of
`L_J` over every test scheme, all three membership conditions agree:

- the preimage under `Int(n)` of the dynamic parabolic of `zeta`, and the
  dynamic parabolic of `eta`;
- the corresponding dynamic centralizers;
- the corresponding dynamic unipotent subgroups.

The proof takes `mu` standard for `J` from `StandardCocharacterStatement`,
and lets `xi` be the inverse transport of `zeta` by the actual scheme
normalizer point corresponding to `n`. Pairing equivariance identifies
`⟨a,xi⟩` with `⟨w a,zeta⟩`. The root condition makes `xi` zero on `K` and
positive on `J \ K`. Finiteness of the simple roots gives an integer `m`
such that `eta = xi + m • mu` is standard for `K`: outside `J`, choose `m`
larger than every negative pairing of `xi`.

A point of `L_J` is centralized by `mu` and hence by `m • mu`.
The private orbit calculation proves that adding a cocharacter centralizing
the point leaves its conjugation orbit unchanged. Unfolding the dynamic
definitions then gives the parabolic, centralizer and unipotent membership
equivalences. Transport of dynamic subgroups under an inner isomorphism
identifies the inverse-transported cocharacter with preimage under `Int(n)`.

## Functors and actual rational points

`pointSourceFunctorIdentities_of_pairingFaces` retains the same assumptions.
The equality clauses of `StandardCocharacterStatement` identify the standard
subgroups of `I` and `K` with the three dynamic subgroups of the chosen standard
cocharacters. The membership comparison gives all three identities

`L_J ⊓ comap(Int(n), F_I) = L_J ⊓ F_K`,

where `F` is respectively the standard Levi, parabolic or unipotent subgroup
functor. These equalities hold on every test scheme and for every actual lift.

`pointSourceIntersectionIdentities_of_pairingFaces` additionally assumes
`StandardLeviIntersectionStatement`. It evaluates the three functor equalities
at the identity test scheme over the field. The published
`SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map` identifies the
preimage with the image under conjugation by `n⁻¹`, giving the exact
`geometricSourceIntersection` convention. Since `K ⊆ J`, the retained Levi
intersection statement gives `L_K ≤ L_J`, so the Levi intersection simplifies
to `L_K`. Restricting the other two identities to `L_J` removes the redundant
intersection via `Subgroup.inf_subgroupOf_left`. The result is precisely
`PointSourceIntersectionIdentities i ν cs`, with all representatives and lifts
quantified.

`pointSourceIntersectionIdentities` composes the proved face condition with
this rational-point evaluation. Its complete scope retains `hN,hZ`, the actual
Coxeter system, both root comparisons, `StandardCocharacterStatement`,
connected reductivity, maximal splitness, genericity, affineness, monicity,
finite simple labels and `StandardLeviIntersectionStatement`.
There is no extra face condition or subgroup equality among its premises.
The resulting proposition is exactly `PointSourceIntersectionIdentities i ν cs`.

## Provenance and scope

The private orbit, inverse-transport and finite-face shift arguments adapt
Worker 1493's `StandardSourceTwistedIntersectionReduction`; they remain private
to avoid duplicate declaration names. The point-Weyl pairing adapter, dynamic
centralizer case, three functor identities and rational-point evaluation are
the present internal extension. The root-condition discharge uses Worker 181's
`RationalTwistedRootSupport`: it proves inverse positivity on the zero face by
positive-root induction, proves simplicity of a transported zero-pairing simple
root by indecomposability, and applies the signed simple-reflection comparison
to identify the intrinsic intersection labels. All steps use the existing
dynamic, lattice, normalizer and subgroup definitions and internal derived
proofs, without an additional literature claim.

The standard cocharacter and Levi intersection statements, and both point and
root-sign comparisons, remain inputs at their target scopes.
No topology or representation data are used in these proof bodies; in
particular they use no Langlands classification, character independence,
geometric lemma, adjointness or cuspidal-support theorem.
Empty simple-root types and arbitrary normalizer lifts are allowed.
This focused helper does not prove geometric expansion, the longest-survivor
comparison or the whole
`RationalJacquetCompatibilityStatement`.
