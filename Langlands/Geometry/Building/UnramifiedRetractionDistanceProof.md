# The retraction distance on the maximal-unramified building

This module proves the published proposition
`Langlands.Geometry.Building.MaximalUnramified.RetractionDistanceStatement.{u}`
(module `Langlands.Geometry.Building.UnramifiedBuildingMetricReduction`) at an
arbitrary universe `u`:

    theorem MaximalUnramified.retractionDistance : RetractionDistanceStatement.{u}

The proof adds no hypothesis on `F`, `H` or `B`. It uses the given inertia fixed
field `K = inertiaFixedField F` and its prescribed valuation. It also uses the
supplied quotient `B.ReducedBuilding` with its existing `H(K)`-action, the
existing apartment `B.Apartment`, the apartment map `B.apartmentMap` and
`KPApartmentData.rootDistance`. A building datum
`B : MaximalUnramified.BuildingData F H` is by definition an
`IntegerValuationBuildingData (valuation F) H`. The final step applies the general
theorem `IntegerValuationBuildingData.exists_retractionDistance` with the published
order-one unit `exists_order_eq_one F`.

## Notation

Fix `B : IntegerValuationBuildingData v G` over a field `k` with a valuation
`v : k → ℤ ∪ {0}` that has an order-one unit (`hunit`). In this section:

- `[a]` means `B.apartmentMap a`, the class of `(1, a)`.
- `g • x` is the action of `g ∈ G(k) = rationalPoints G` on `B.ReducedBuilding`.
- The facet of a point `c` is `facet B.affineRoots c`; it is a chamber when `c` is
  regular (`IsRegular`).
- `P_C` is the sharp fixer `B.apartment.sharpFixer (facet B.affineRoots c)` of
  that facet.
- `N` is the group `normalizerPoints B.i`.

The apartment has the Euclidean root metric of the statement module:
`dist a b = ‖a -ᵥ b‖`, with norm `RootTranslationMetric`. By the published
`rootDistance_eq_dist` this equals `B.apartment.rootDistance a b`. The module
installs the same local instances as the `RootMetric` section of
`IntegerValuationBuildingMetricReduction`, with the same two `backward.isDefEq` options.

## Declarations

The generic construction is imported from
`IntegerValuationRetractionDistance`; its public declarations and proofs are
unchanged by this import separation. All the declarations below are in namespace
`Langlands.Geometry.Building.IntegerValuationBuildingData`, except the last.

| Lean name | Kind | Content |
| --- | --- | --- |
| `exists_smul_apartmentMap_pair` | theorem | `HasCommonApartments` unfolded: any `x, y` are `g • [a], g • [b]` |
| `retractionDistance` | def | the root distance of chosen common-apartment coordinates of `x, y` |
| `retractionDistance_smul_apartmentMap` | theorem | `d (g • [a]) (g • [b]) = dist a b` for all `g, a, b` |
| `retractionDistance_smul` | theorem | `d (h • x) (h • y) = d x y` |
| `smul_apartmentMap_eq_of_mem_sharpFixer_facet` | theorem | `P_C` fixes `[y]` for every `y` in the closure of the facet of `c` |
| `exists_sharpFixer_facet_normalizer_mul` | theorem | for regular `c, d`, every `g` is `p * n * q` with `p ∈ P_C`, `n ∈ N`, `q ∈ P_D` |
| `eq_of_forall_mem_facet_norm_vsub_eq` | theorem | if `‖z - b'‖ = ‖z - b‖` for all `z` in the open chamber of a regular `c`, then `b = b'` |
| `eq_of_mem_sharpFixer_facet_smul_apartmentMap_eq` | theorem | if `p ∈ P_C` and `p • [b] = [b']`, then `b = b'` |
| `exists_sharpFixer_facet_smul_apartmentMap_eq` | theorem | every `x` is `p • [b]` for some `p ∈ P_C` and `b` |
| `chamberRetraction` | def | `ρ_{A,C}`: a chosen `b` with `p • [b] = x` for some `p ∈ P_C` |
| `exists_smul_apartmentMap_chamberRetraction` | theorem | the defining property of `chamberRetraction` |
| `chamberRetraction_eq` | theorem | `p ∈ P_C` and `p • [b] = x` imply `ρ x = b` |
| `chamberRetraction_apartmentMap` | theorem | `ρ [b] = b` |
| `dist_chamberRetraction_le_of_mem_facetClosure` | theorem | for `x, y` in one closed facet, `dist (ρ (g • [x])) (ρ (g • [y])) ≤ dist x y` |
| `exists_retractionDistance` | theorem | the three clauses of the statement for `B`, given `hunit` |
| `MaximalUnramified.retractionDistance` | theorem | `RetractionDistanceStatement.{u}` |

## Proof

### The distance

The published `IntegerValuationBuildingData.hasCommonApartments hunit`
(module `IntegerValuationCommonApartmentsProof`) gives common translated
apartments. For any `x, y` it supplies `h, a', b'` with `h • [a'] = x` and
`h • [b'] = y`. The function `retractionDistance hcommon x y` is
`B.apartment.rootDistance a' b'` for one such choice.

It does not depend on the choice. Suppose `x = g • [a]` and `y = g • [b]`. Then
`(g⁻¹ h) • [a'] = [a]` and `(g⁻¹ h) • [b'] = [b]`. The published
`KPApartmentData.norm_vsub_eq_of_two_apartmentMap_eq` (module
`GenericApartmentPairNormalizer`) then gives `‖a - b‖ = ‖a' - b'‖`. This is
`retractionDistance_smul_apartmentMap`.

- **Clause 2** is the case `g = 1`.
- **Clause 1** follows by writing `x = g • [a]` and `y = g • [b]`, so that
  `h • x = (h g) • [a]` and `h • y = (h g) • [b]`.

### Sharp fixers of chambers

The published `sharpFixer_facet_le_singleton_of_mem_facetClosure` says that `P_C`
is contained in the sharp fixer of each point `y` of the closure of the facet of
`c`. With `sharpFixer_le_reducedFixer` and `mem_reducedFixer`, `P_C` fixes `[y]`.

**Mixed factorization** (`exists_sharpFixer_facet_normalizer_mul`). Let `c, d` be
regular, with chambers `C, D`.

1. Affine Weyl chamber transitivity (`affineChamberSimpleTransitivity`, using
   `isAffineRootSystemWithRankZero_affineRoots hunit`) and the published
   `affineWeylGroup_le_range` give `m ∈ N` with `m • C = D`.
2. The published sharp chamber cover `mem_sharpChamberNormalizerCover hunit`
   writes `g * m = p * n * q` with `p, q ∈ P_C` and `n ∈ N`.
3. By `sharpFixer_le_comap`, `m q m⁻¹ ∈ P_{m C} = P_D`.
4. Hence `g = p * (n m⁻¹) * (m q m⁻¹)`.

This is the argument of `IntegerValuationCommonApartmentsProof`, with `P_C` on the
left and `P_D` on the right.

### The chamber retraction

Fix a regular point `c`.

**Existence.** Write `x = g • [a]`. Local finiteness
(`isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs`) and
`exists_regularPoint_closure` give a regular `d` whose facet closure contains `a`.
Factor `g = p n q` with `p ∈ P_C` and `q ∈ P_D`. Then `q` fixes `[a]` and `n • [a] = [n • a]`
(`normalizer_smul_apartmentMap`), so `x = p • [n • a]`.

**Uniqueness.** Let `p ∈ P_C` with `p • [b] = [b']`. For each `z` in the open
chamber of `c`, `p` fixes `[z]`. The normalizer lemma applied to `p`, with
`p • [z] = [z]` and `p • [b] = [b']`, gives `‖z - b'‖ = ‖z - b‖`. Now apply
`eq_of_forall_mem_facet_norm_vsub_eq` with `w = b' - b` and `u = c - b'`:

1. By `eventually_sign_smul_vadd` and `exists_pos_of_eventually`, there is `ε > 0`
   such that `ε • w + c` has the same nonzero root signs as `c`. Since `c` is
   regular, this point lies in the facet of `c`.
2. Equidistance at `c` gives `‖u‖² = ‖u + w‖²`.
3. Equidistance at `ε • w + c` gives `‖ε w + u‖² = ‖ε w + u + w‖²`.
4. Expanding with `norm_add_sq_real` and the bilinearity of the inner product
   gives `2⟨u,w⟩ + ‖w‖² = 0` and `2ε‖w‖² + 2⟨u,w⟩ + ‖w‖² = 0`.
5. Therefore `ε‖w‖² = 0`, so `w = 0` and `b = b'`.

The two points use the inner product `RootTranslationMetric.innerProductSpace`.
No Tits system is used.

`chamberRetraction hunit hc x` is the point `b` chosen by existence. By uniqueness,
applied to `p⁻¹ p'`, any `p ∈ P_C` with `p • [b] = x` gives `ρ x = b`
(`chamberRetraction_eq`). With `p = 1` this gives `ρ [b] = b`.

### Nonexpansion

Fix `g` and a point `p₀` of the apartment. Choose a regular `d` whose facet closure
contains `p₀`, and factor `g = p n q` with `p ∈ P_C` and `q ∈ P_D`. Let `z` be in
the closure of the facet of `p₀`. By `mem_facetClosure_trans`, `z` is in the
closure of `D`, so `q` fixes `[z]` and `g • [z] = p • [n • z]`. Hence
`ρ (g • [z]) = n • z`. The normalizer lemma gives `dist (n x) (n y) = dist x y`.
This is `dist_chamberRetraction_le_of_mem_facetClosure`.

The published `AffineRootSystem.dist_le_of_forall_mem_facetClosure` (module
`FacetClosureLipschitz`) uses the local finiteness bound
`finite_bounded_at`. It turns this local estimate into
`dist (ρ (g • [u])) (ρ (g • [w])) ≤ dist u w` for all apartment points `u, w`.
Writing `x = g • [u]` and `y = g • [w]` in a common apartment, the right side is
`d x y`.

### Clause 3

Given an apartment point `a`, choose a regular `c` whose facet closure contains
`a` and take `ρ = chamberRetraction hunit hc`. Then:

- `ρ [b] = b` holds by `chamberRetraction_apartmentMap`.
- Nonexpansion is the previous section.
- For the distance from `a`, take `p ∈ P_C` with `p • [ρ x] = x`. Since `p` also
  fixes `[a]`, `d ([a], x) = d (p • [a], p • [ρ x]) = dist a (ρ x)`.

## Literature

The proof follows the role of the cited results in Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach* (2023), as listed in the paired Markdown of
`UnramifiedBuildingMetricReduction`:

- Proposition 4.2.1: the `G(k)`-invariant distance restricting to `d_A`.
- Proposition 1.5.24 and Definition 1.5.25: the retraction `ρ_{A,C}`.
- Lemma 4.2.2: `ρ_{A,C}` is the identity on `A`. It preserves distances from
  points of the closure of `C` (2) and does not increase distances (3).

The Lean route is internal and need not follow KP's proofs:

- Uniqueness of the retraction uses equidistance on the open chamber.
- Nonexpansion uses the Library's facet-closure Lipschitz lemma along segments.

The local-field analogue of the retraction construction is the Library module
`ValuationBuildingRetraction`.

## Ingredients and constraints

- The contract allows the proof of `MaximalUnramified.CommonApartmentsStatement`.
  It enters through `IntegerValuationBuildingData.hasCommonApartments`.
- This wrapper imports `IntegerValuationRetractionDistance` and
  `UnramifiedBuildingMetricReduction`. The generic module imports
  `IntegerValuationBuildingMetricReduction`, `IntegerValuationCommonApartmentsProof`,
  `GenericApartmentPairNormalizer`, `FacetClosureLipschitz` and `AffineWeylFacetFixing`.
- Their Library import closure contains no proof of any of the following:
  `UnramifiedBuildingMetricStatement`, `UnramifiedTwistedChamberStatement`,
  `UnramifiedTwistedFixedPointStatement`,
  `LocalSimplyConnectedUnramifiedChamberStatement`,
  `LocalSimplyConnectedUnramifiedIntegralTwistStatement`,
  `LocalSimplyConnectedUnramifiedCocycleVanishingStatement`,
  `LocalSimplyConnectedGaloisCocycleVanishingStatement` or
  `LocalSimplyConnectedCocycleVanishingStatement`.
- `UnramifiedBuildingMetricReduction` proves only the implication
  `UnramifiedBuildingMetricReductionStatement`.

## Overlap

Worker 202's staged candidate `59b3a979-6df4-45fa-877c-b3c71a5f3655` (module `MaximalUnramifiedRootDistance`,
`BuildingData.invariantRootDistance`) describes the same chart distance: the root
distance read in a common translated apartment. It was unpublished at this
module's Library base `c0debd6f`, so this module defines `retractionDistance`
itself. A later integration may identify the two.

The import separation retains this theorem and its exact target. Consumers that
need only the generic distance and chamber retractions can import
`IntegerValuationRetractionDistance` without the downstream unramified metric
statement modules. Worker 5428 authored the construction; Worker 202 separated
the generic import boundary.
