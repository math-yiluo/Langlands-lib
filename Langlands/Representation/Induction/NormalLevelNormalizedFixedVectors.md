# Normalized induced fixed vectors and the literal Levi intersection

This internal construction extends the actual normal-level evaluation criterion
to the published normalized induction functor. The group universe and the
coefficient-vector universe are independent.

Let `P = M ⋉ U` be an actual semidirect decomposition in a nonarchimedean
locally compact group, with `U` and `P` closed, and let `K` be compact open.
Assume that the actual Levi projection sends every element of `P ∩ K`
into `M ∩ K`. For any smooth complex representation `A` of `M`,
`inducingRepresentation_fixedVectors_eq` identifies, as submodules of the
same coefficient space, the fixed space of the normalized inducing action
under `P ∩ K` with the fixed space of `A` under the literal inverse image
`K.comap M.subtype`.

The half-modulus is one on `P ∩ K` by the published compact-intersection
theorem. Projection stability proves that Levi-fixed vectors are fixed by
the coefficient intersection. Conversely the projection is the identity
on `M`, so coefficient-fixed vectors are fixed under `K ∩ M`.

For a subgroup `K₀` normalizing `K`, `normalLevelNormalizedEvaluation`
restricts actual normalized induced fixed vectors to `K₀`, taking values in
this literal Levi fixed space. If `G = P K₀`, this map is injective.
The nontriviality criterion says that the normalized induced `K`-fixed
space is nontrivial exactly when the `K ∩ M`-fixed coefficient space is.
These conclusions follow from the actual normal-level evaluation theorem
and the coefficient fixed-space equality.

The purely algebraic helper
`IsSemidirectDecomposition.projection_mem_of_iwahoriIntersection` discharges
projection stability from the literal ordered intersection factorization
`(K ∩ Ubar)(K ∩ M)(K ∩ U)` and triviality of `P ∩ Ubar`.
For an element in `P ∩ K`, its first factor lies in `P ∩ Ubar`, hence is
the identity; the remaining middle factor is its Levi projection.
Only surjectivity of the stated bijective factorization is used.

The provenance is this internal argument using the published actual
semidirect projection, compact half-modulus and smooth induction
constructions. No admissibility, finite length, compactness of `K₀`,
or containment `K ≤ K₀` is assumed. Projection stability and the
opposite-intersection condition remain explicit in their respective
generic declarations. This result does not assert generation by fixed
vectors, visibility of each constituent, or the host fixed-vector
category theorem.
