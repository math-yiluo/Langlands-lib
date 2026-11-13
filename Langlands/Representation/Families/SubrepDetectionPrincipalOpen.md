# Irreducibility neighborhoods from fixed-vector detection of subrepresentations

Author: Worker 52. Module
`Langlands.Representation.Families.SubrepDetectionPrincipalOpen`, namespace
`Langlands.Renard.AlgebraicFamily.SubrepDetectionPrincipalOpen`. Internal
support for the proof of `ConditionalParabolicGenericIrreducibilityStatement`
(module `Langlands.Representation.Plancherel.ParabolicGenericIrreducibilityProof`),
through `AdmissibleInducedIrreducibilityOpen`.

## Purpose and provenance

The Library's compact-compression neighborhoods
(`CompactCompressionMatrices.isIrreducible_of_fixedMatrix`,
`CompactCompressionPrincipalOpen.exists_regular_principal_neighborhood` and
`exists_polynomial_principal_neighborhood_of_family`) formalize the flatness
argument in the proof of Renard, *Représentations des groupes réductifs
p-adiques* (9 July 2026), VI.8.4, printed pp. 192–193 / PDF pp. 198–199
(`renard-2026-representations-groupes-reductifs-padiques`). They assume that
one compact open subgroup `K` detects every irreducible subquotient of every
fiber. The matrix argument uses only two consequences of that assumption. This
module states those two consequences as a predicate and repeats the
neighborhood argument under it. This is derived internal content. No new
source claim is made.

## Definition

`IsSubrepDetected ρ K` for a complex representation `ρ` of a group and a
subgroup `K` means:

1. every nonzero subrepresentation `S` contains a nonzero `K`-fixed vector;
2. every subrepresentation `S` that contains all `K`-fixed vectors is `⊤`.

## Results

- `IsSubrepDetected.of_equiv`: the predicate is transported along an
  equivariant linear equivalence. Part 1 uses the preimage of `S`. Part 2 is the
  published `NormalizedJacquetBridge.generation_of_equiv`.
- `IsSubrepDetected.exists_fixed_ne_zero`: an irreducible detected
  representation has a nonzero `K`-fixed vector (part 1 with `S = ⊤`).
- `exists_contragredient_fixed_ne_zero`: if a compact open `L` fixes a nonzero
  `v`, then `L` fixes a nonzero smooth functional. Choose a functional on the
  `L`-fixed space that is nonzero at `v`. Lift it with the published bijection
  `smoothDualFixedRestriction_bijective` between the `L`-fixed vectors of the
  contragredient and the dual of `V^L`.
- `contragredient_fixed_eq_zero`: if `L` fixes no nonzero vector, then `L` fixes
  no nonzero smooth functional. This is the injectivity half of the same
  bijection.
- `isIrreducible_of_fixedMatrix_of_subrepDetected`: the analogue of
  `isIrreducible_of_fixedMatrix`. Let `A` be nontrivial and detected by `K`, and
  let the compressed matrices `fixedMatrix A K hK e` form an irreducible family.
  Then `A` is irreducible. Proof: for a subrepresentation `S`, the coordinates
  of `S ∩ A^K` form a subspace `U` of `ℂⁿ`. `U` is invariant under every matrix,
  by `fixedMatrix_mulVec` and `averageMap_mem`. If `U = 0` then `S` has no
  nonzero `K`-fixed vector, so `S = ⊥` by part 1. If `U = ℂⁿ` then
  `A^K ≤ S`, so `S = ⊤` by part 2.
- `exists_regular_principal_neighborhood_of_subrepDetected`: the analogue of
  `CompactCompressionPrincipalOpen.exists_regular_principal_neighborhood`, with
  the subquotient-detection hypothesis replaced by `IsSubrepDetected` of every
  fiber `D x`. At the irreducible fiber `x₀`, detection gives a nonzero fixed
  vector, so the index type is nonempty. `fixedMatrix_isIrreducible` and the
  published `LocalizedMatrixPrincipalOpen.exists_regular_principal_neighborhood`
  give `f` with `χ x₀ f ≠ 0`, on whose nonvanishing locus the specialized
  matrices are irreducible. The fiber is then irreducible there by the previous
  item.
- `exists_polynomial_principal_neighborhood_of_family_of_subrepDetected`: the
  analogue of `exists_polynomial_principal_neighborhood_of_family`. Let a global
  coefficient family (`IsGlobalCoefficientFamily A M e D`) over the unramified
  characters of a connected reductive `M` be given, with every fiber detected by
  one compact open `K`. If `D χ₀` is irreducible, there is a polynomial `p` such
  that `χ₀` lies in `rationalUnramifiedPrincipalOpen M hM p` and every `D χ` with
  `χ` in that set is irreducible. Proof: the previous item with the trivial
  localization `S = B`, `g = 1`, transported to polynomials by
  `principalOpen_rationalRegularPolynomial`.

## Checks

The module compiles with zero errors and zero warnings in the environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`.
