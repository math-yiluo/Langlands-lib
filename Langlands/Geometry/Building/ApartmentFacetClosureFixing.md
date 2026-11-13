# Fixing segments and closed facets in the reduced quotient over any field

Module `Langlands.Geometry.Building.ApartmentFacetClosureFixing`.

## Results

All results in namespace `Langlands.Geometry.Building.KPApartmentData` are about
apartment data `D : KPApartmentData i ω` over an **arbitrary field** `k`, with
`hG : IsConnectedReductive G` and `hi : IsMaximalSplitTorus i`. No apartment axioms,
no topology and no local-field structure are assumed. `D.apartmentMap` is the map of
the apartment into the reduced quotient on which `G(k)` acts.

- `eval_neg_character_apply`: `eval S (-b) w = -eval S b w`.
- `exists_genericCocharacter_eval_nonneg_of_isMaximalSplitTorus`: for every
  `w : V S` there is a generic cocharacter `ν` such that every relative root `b`
  with `⟨b, ν⟩ > 0` satisfies `b(w) ≥ 0`.
- `smul_eq_self_of_unipotent_mul_smul_apartmentMap_eq_of_isMaximalSplitTorus`: if
  `v * n` fixes `D.apartmentMap x`, where `v` lies in the unipotent group of a generic
  cocharacter `ν` and `n ∈ N(k)`, then `n • x = x` in the apartment.
- `positiveChamberRootGroups_le_sharpFixer_vadd`: the zero-depth root groups at `x`
  for roots positive on `ν` lie in the sharp fixer of `w + x` whenever every such
  root is nonnegative on `w`.
- `smul_apartmentMap_lineMap_eq` (**two-point fixation**): if `h ∈ G(k)` fixes
  `D.apartmentMap y` and `D.apartmentMap z`, then it fixes
  `D.apartmentMap (lineMap y z t)` for every `t ∈ [0, 1]`.
- `fixedApartmentCoordinates h o`: the set of vectors `v` for which the actual
  rational element `h` fixes `D.apartmentMap (v +ᵥ o)` in the original reduced
  quotient.
- `convex_fixedApartmentCoordinates`: this set is convex over the reals for every
  rational element `h` and apartment origin `o`.
- `smul_apartmentMap_vadd_eq_of_mem_convexHull`: if `h` fixes `D.apartmentMap (v +ᵥ o)`
  for every `v` in a finite set `s`, it fixes `D.apartmentMap (v +ᵥ o)` for every `v`
  in the real convex hull of `s`.
- `smul_apartmentMap_eq_of_mem_facetClosure`: assume additionally
  `AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots`. If `h` fixes
  `D.apartmentMap q` for every vertex `q` (`AffineRootSystem.IsVertex`) lying in the
  closed facet `AffineRootSystem.facetClosure D.affineRoots p`, then `h` fixes
  `D.apartmentMap x` for every `x` in that closed facet.

In namespace `Langlands.Geometry.Building.IntegerValuationBuildingData`:

- `smul_apartmentMap_eq_of_vertices_fixed`: for `B : IntegerValuationBuildingData v G`
  with `AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots`, the body of
  `B.ClosedFacetsFixedByVertices` holds. It is the previous result applied to
  `B.apartment`, `B.isConnectedReductive` and `B.isMaximalSplitTorus`.

## Proof

**Generic cocharacter adapted to `w`.** The finitely many relative roots and
`RootFaceCone.exists_int_sign_realization` give an integral `μ` with
`⟨b, μ⟩ < 0` whenever `b(w) < 0`. With a generic `ν₀` and an integer `M` larger
than every `|⟨b, ν₀⟩|`, the cocharacter `M μ + ν₀` is generic, and a root positive
on it cannot be negative on `w`.

**Bruhat step.** Write the stabilizer element at `x` as `s m` with `s` in the sharp
fixer and `m ∈ N(k)` fixing `x`
(`ApartmentQuotient.mem_stabilizer_apartment_iff`), and split
`s = v' w q` by `sharpFixer_subset_mul_sharpNormalizerStabilizer` for `-ν`. Then
`q m n⁻¹ = w⁻¹ (v'⁻¹ v)` with `w⁻¹` in the opposite unipotent group and `v'⁻¹ v` in
the unipotent group of `ν`, so `normalizer_eq_one_of_unipotent_product` gives
`q m n⁻¹ = 1`. Hence `n = q m` fixes `x`.

**Two-point fixation.** Write `z = w +ᵥ y` and pick `ν` adapted to `w`. Decompose
`h = s m` at `y` and `s = u v q` as above, so `h = u (v n)` with `n = q m ∈ N(k)`
fixing `y`, `u` in the zero-depth positive root groups at `y`, `v` in the unipotent
group of `-ν`.

1. `u` fixes the ray `r w +ᵥ y`, `r ≥ 0` (filtration shift `filtration_mk_vadd`),
   so in particular fixes `z`. Hence `v n` fixes `z`.
2. The Bruhat step at `z` gives `n • z = z`; therefore `v` fixes `z`, and
   `mem_positiveRootGroups_of_mem_unipotent_of_smul_apartmentMap_eq` places `v` in the
   zero-depth positive root groups for `-ν` at `z`.
3. Every relative root is matched by its negative (`neg_mem_relativeRoots_of_rankOne`),
   so roots positive on `-ν` are nonnegative on `(1 - t)(-w)`, and `v` fixes
   `lineMap y z t = (1 - t)(-w) +ᵥ z`.
4. `n` acts by the affine map `normalizerAffineEquiv n`, which fixes `y` and `z` and
   hence `lineMap y z t`.
5. `u` fixes `lineMap y z t = t w +ᵥ y` by step 1.

Composing gives `h • D.apartmentMap (lineMap y z t) = D.apartmentMap (lineMap y z t)`.

**Fixed coordinate sets.** The definition is the inverse image of the original
quotient fixed locus under `v ↦ D.apartmentMap (v +ᵥ o)`. Two-point fixation and
`AffineMap.lineMap_vadd_lineMap` prove that it contains the segment joining any
two of its vectors, which is exactly convexity.

**Convex hulls.** Induction on the finite set, using `convexHull_insert` and
`AffineMap.lineMap_vadd_lineMap` to reduce to two-point fixation.

**Closed facets.** Transport the affine roots along `AffineEquiv.vaddConst ℝ p`
(`IsAffineRootSystemWithRankZero.transport`) with the root translation metric on the
translation space. `AffineRootSystem.convexHull_facetClosureVertexFinset` identifies
the transported closed facet with the convex hull of the finite set of its vertices;
`mem_facetClosure_transportedRoots_iff` and `isVertex_transportedRoots_iff` translate
membership and vertex status back. The convex-hull result then applies.

## Provenance

Internal. The two-point argument follows the proof of Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach*, Lemma 7.7.4 (printed pp. 268–269), which uses the
generic-point decomposition, the Bruhat decomposition and the triviality of
`U(ν) ∩ U(-ν)` in the same way. The adapted generic cocharacter, the convex-hull
induction and the facet-closure reduction are routine additions for the Lean
statement. The Lean proof uses only Library results valid over any field, not the
local-field results of `ValuationBuildingData`.
