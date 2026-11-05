# Proof of the torus-weighted triangular coordinates

This module proves the Library proposition
`Langlands.GroupScheme.PositiveTorusTriangularCoordinatesStatement` (module
`Langlands/GroupScheme/Rational/PositiveTorusTriangularCoordinates`):

```
theorem positiveTorusTriangularCoordinates :
    PositiveTorusTriangularCoordinatesStatement.{u}
```

The statement says the following. Let `F` be a field of characteristic zero, `G` a connected
reductive group over `F`, `i : T ⟶ G` a maximal split torus and `ν` a generic cocharacter. Let
`ι : N ⟶ G` be the standard unipotent subgroup `N = Standard.unipotentScheme i ν ∅`. Then there
are global functions `t₀, …, t_{d-1}` on `N`, polynomials `P_k`, and characters `w_k` of `T`
such that:

- `MvPolynomial.aeval t : F[X₀, …, X_{d-1}] → AffineCoordinateRing F N.X` is bijective;
- every variable of `P_k` has index `< k`, and `(x * y)_k = x_k + y_k + P_k(x_j, y_j)` for all
  points `x`, `y` of `N` in every `F`-algebra;
- if `ι(y) = i(s) ι(x) i(s)⁻¹`, then `y_k = w_k(s) x_k`;
- every `w_k` is a positive relative root, and each positive relative root `β` occurs as `w_k`
  for exactly `dim_F 𝔤_β` indices `k`.

The hypothesis that `ν` is generic is not used.

The module also proves a comparison of two coordinate rings of an affine group. The Library's
torus-weight results for an affine group `H` are stated for its chosen coordinate algebra
`CharacterUnits.Coord H = Lie.coordinateAlgebra H`. That algebra is a fixed affine presentation
of `H`, and points are evaluated through `Lie.pointCoordinates H`. The statement instead uses
the ring of global sections `AffineCoordinateRing k H.X`, with evaluation
`H.affinePointEvaluation A x`. The section `CharacterUnits` identifies the two rings compatibly
with evaluation at points.

## Comparison of coordinate rings

Namespace `Langlands.GroupScheme.CharacterUnits`, for a group `H` over a field `k` with
`[IsAffineHom H.X.hom]` and `[IsAffine H.X.left]`. `GaloisPoint.coordinates k H A` is the
Library bijection between points of `H` with coefficients in `A` and `k`-algebra maps
`AffineCoordinateRing k H.X → A`. Its value on a global section is the evaluation
`affinePointEvaluation` (`GaloisPoint.coordinates_apply`).

- `coordinates_affinePointMap`: for `f : A →ₐ[k] B`, the global-section coordinates of the
  base change of `x` along `f` are `f ∘ coordinates x`. This uses only `[IsAffine H.X.left]`.
- `sectionPoint H` (a definition): the point of `H` with coefficients in
  `AffineCoordinateRing k H.X` whose global-section coordinates are the identity.
- `affinePointMap_sectionPoint`: every point `x` of `H` over `A` is the base change of
  `sectionPoint H` along `coordinates x`.
- `coordToSections H : Coord H →ₐ[k] AffineCoordinateRing k H.X` (a definition): the chosen
  coordinates of `sectionPoint H`.
- `sectionsToCoord H : AffineCoordinateRing k H.X →ₐ[k] Coord H` (a definition): the
  global-section coordinates of the universal point `CharacterUnits.universalPoint H`.
- `affinePointEvaluation_coordToSections`: for every point `x` over `A` and every `c : Coord H`,
  `H.affinePointEvaluation (CommAlgCat.of k A) x (coordToSections H c) =
  Lie.pointCoordinates H x c`. `affinePointEvaluation_coordToSections'` is the same statement
  for a bundled algebra `A : CommAlgCat k`.
- `pointCoordinates_sectionsToCoord`: for every point `x` over `A` and every global section `a`,
  `Lie.pointCoordinates H x (sectionsToCoord H a) =
  H.affinePointEvaluation (CommAlgCat.of k A) x a`.
- `coordToSections_sectionsToCoord` and `sectionsToCoord_coordToSections`: the two maps are
  mutually inverse.
- `coordSectionsEquiv H : Coord H ≃ₐ[k] AffineCoordinateRing k H.X` (a definition), with
  `coordSectionsEquiv_apply`: the resulting algebra isomorphism, whose underlying map is
  `coordToSections H`.

Proofs. `coordinates_affinePointMap` is the Library naturality of evaluation
(`affinePointEvaluation_map`). `affinePointMap_sectionPoint` follows from it by injectivity of
`coordinates`. For `affinePointEvaluation_coordToSections`, write `x` as the base change of
`sectionPoint H` along `coordinates x`. Then use the naturality of the chosen coordinates
(`Lie.pointCoordinates_naturality`). `pointCoordinates_sectionsToCoord` is the same argument with
the universal point (`affinePointMap_universalPoint`) and `coordinates_affinePointMap`. For the
inverse laws, evaluate at the universal point and at `sectionPoint H`: the chosen coordinates of
the universal point are the identity (`pointCoordinates_universalPoint`), and the global-section
coordinates of `sectionPoint H` are the identity by definition.

## Proof of the main theorem

Fix `F`, `G`, `i`, `ν` as above. Then `G` is smooth (`IsConnectedReductive.smooth`), and `T` is
a split torus (the first component of `IsMaximalSplitTorus`). Let
`b = Standard.unipotentAction i ν hT` be the conjugation action of `T` on `N`
(`TorusUnipotence/StandardUnipotentAction`). That module shows `N` is smooth.

1. **Coordinates.** Every character in `CoordinateWeights.support b`, that is, the weight of
   a nonzero eigenfunction in the augmentation ideal, pairs positively with `ν`
   (`Standard.pairing_pos_of_mem_support`). So `TorusUnipotence.exists_positiveWeight_coordinates`
   gives `d`, weights `w : Fin d → characterLattice T`, and `t : Fin d → Coord N` with:
   `aeval t` bijective; `t j` a `w j`-eigenfunction of `b`; `t j` vanishing at the identity;
   `⟨w j, ν⟩ > 0`; and `j ↦ ⟨w j, ν⟩` monotone. `TorusUnipotence.exists_triangular_mul` then gives
   polynomials `P j` with variables of index `< j` such that
   `(x * y)(t j) = x(t j) + y(t j) + P_j(x(t i), y(t i))`, evaluated with
   `Lie.pointCoordinates`.
2. **Transport to global sections.** The witnesses are `d`, `t' k = coordToSections N (t k)`, the
   same `P`, and the same `w`. We have `aeval t' = coordToSections N ∘ aeval t`
   (`MvPolynomial.comp_aeval`), which is bijective as the composite of `aeval t` with
   `coordSectionsEquiv N`. The variable condition on `P` is unchanged. Rewriting each
   evaluation of `t' k` with `affinePointEvaluation_coordToSections'` turns the triangular group
   law into the law from step 1.
3. **Torus equivariance.** Suppose `ι(y) = i(s) ι(x) i(s)⁻¹`. By
   `Standard.unipotentAction_act_comp`, `ι(b.act s x)` has the same value, and `ι` is a
   monomorphism, so `y = b.act s x`. Since `t k` is a `w k`-eigenfunction
   (`CoordinateWeights.IsEigenfunction`), `(b.act s x)(t k) = w_k(s) · x(t k)`. Rewrite both
   evaluations with `affinePointEvaluation_coordToSections'`.
4. **Weights are positive roots.** By `TorusUnipotence.finrank_actionWeightSpace`, the
   `w k`-weight space of `b` on `Lie(N)` has dimension `#{j | w j = w k}`, which is positive
   because it contains `k`. So the weight space is nonzero, and
   `Standard.actionWeightSpace_unipotentAction_ne_bot_iff` gives
   `w k ∈ positiveRelativeRoots i ν`.
5. **Multiplicities.** For `β ∈ positiveRelativeRoots i ν`,
   `#{k | w k = β} = finrank (actionWeightSpace b β)` by `finrank_actionWeightSpace`. This equals
   `finrank (weightSpace i β)` by `Standard.finrank_actionWeightSpace_unipotentAction`.

## Provenance

This proves the Library proposition `PositiveTorusTriangularCoordinatesStatement`, an internal
step in the proof of `NormOneRationalQuotientFiniteVolumeStatement` (Getz–Hahn 2024
Theorem 2.6.3). The statement and its literature context (Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, Proposition 2.1.8 and Milne, *Algebraic Groups*, Chapter 14) are
described in `PositiveTorusTriangularCoordinates.md`. The proof does not use exponential maps.
It combines the torus-graded formal smoothness of the coordinate ring
(`TorusUnipotence/PositiveWeightCoordinates`), the Lie multiplicity count
(`TorusUnipotence/LieWeightMultiplicity`), and the dynamic description of `N`
(`TorusUnipotence/StandardUnipotentAction`). The comparison of coordinate rings is routine
bookkeeping between two Library presentations of the same affine scheme.
