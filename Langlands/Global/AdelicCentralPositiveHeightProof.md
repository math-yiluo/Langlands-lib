# Proof of the central norm-one factorization with polynomially bounded height

Authors: Worker 5414 (proof and Markdown); Worker 145 (recheck over the current Library
and Markdown corrections).

This module proves the published proposition
`Langlands.Global.RepresentationGrowth.CentralNormOneHeightFactorStatement`
(module [`AdelicCentralPositiveHeightStatement`](AdelicCentralPositiveHeightStatement.md))
as the theorem

```lean
theorem Langlands.Global.RepresentationGrowth.centralNormOneHeightFactorStatement :
    CentralNormOneHeightFactorStatement.{u}
```

at every universe `u` and without extra hypotheses. The statement is used unchanged.

## What is proved

Let `F : Type u` be a number field, and let `G` be a group scheme over `Spec F` with
`IsAffine G.X.left`. Let `rho : MatrixRepresentation G (Fin N)` be a matrix
representation. Assume `IsConnectedReductive G`, `IsClosedSubgroup rho` and `0 < N`.
Then there are a real `c` and a natural number `e` such that every adelic point
`g : AdelicGroupPoints F G` has a factor `z` with four properties:

1. `z` commutes with every adelic point;
2. `AdelicGroupPoints.finite F G z = 1`;
3. `z⁻¹ * g ∈ AdelicGroupPoints.normOneSubgroup F G`;
4. `adelicHeight F G rho z ≤ c * adelicHeight F G rho g ^ e`.

The constants `c` and `e` are chosen before `g`. Nothing is assumed about splitting,
anisotropy or the rank of the centre. A central split torus of rank zero is included:
then the only positive torus point is `1`, and lemma B below treats this case
separately.

## Published inputs

- `PositiveRealTorus.adelicPositiveDecompositionStatement` (module
  `AdelicPositiveDecompositionProof`). For connected reductive `G` it gives a
  commutative group scheme `T`, a homomorphism `i : T.toGrp ⟶ G` with
  `IsSplitComponent i`, and a continuous group equivalence
  `E : intrinsicSubgroup F T × normOneSubgroup F G ≃ₜ* AdelicGroupPoints F G` with
  `E (a, n) = positivePointMap F G T i a * n`.
- `characterRestrictionFiniteIndexStatement` (module
  `GroupScheme.Rational.CharacterRestrictionFiniteIndexProof`). For a split component
  `i` of a connected reductive group, the range of the character restriction
  `characterRestrict i : X^*(G) → X^*(T)` has finite index.
- `closedImmersionAdelicHeightDomination` (module
  `AdelicRepresentationHeightDominationProof`). If `rho` is a closed embedding of
  positive rank, then for every representation `sigma` of positive rank there are
  `C ≥ 1` and `e : ℕ` with `adelicHeight sigma g ≤ C * adelicHeight rho g ^ e` for
  all adelic points `g`.
- From the positive-torus modules: `PositiveRealTorus.full`,
  `PositiveRealTorus.subgroup_eq_intrinsicSubgroup`,
  `PositiveRealTorus.positivePointMap_commute`,
  `PositiveRealTorus.positivePointMap_apply`,
  `PositiveRealTorus.atFinitePlace_intrinsic`,
  `PositiveRealTorus.coordinates_full`,
  `PositiveRealTorus.characterValue_coordinateCharacter`, and
  `PositiveRealIdeles.absoluteValue_full`.
- `characterNorm_nsmul` (module `AdelicPositiveRootCharacterRelation`) and
  `characterNorm_comp` (module `AdelicGroupNormOneFunctorial`).
- For the finite component: `GroupScheme.affinePointEvaluation_injective` (module
  `GroupScheme.AffinePointTopology`), `AdelicSiegelFactors.evaluation_finite` (module
  `AdelicRationalHeightReduction`) and `atFinitePlace_evaluation` (module
  `AdelicGroupLocalPoints`).

## Implemented proof

The module consists of four groups of lemmas and the main theorem. All are in the
namespace `Langlands.Global.RepresentationGrowth`.

### A. Character norms are polynomially bounded by the height

- `adelicMatrix_lineRepresentation`: for a rational character `χ`, the adelic matrix
  of the `1 × 1` line representation `χ.lineRepresentation` at `g` is the diagonal
  unit matrix of the idele `character F G χ.toMul g`.
- `characterNorm_le_adelicHeight_lineRepresentation`: the normalized idele norm
  `characterNorm F G χ.toMul g` is at most `adelicHeight F G χ.lineRepresentation g`.
  At each infinite and each finite place, the absolute value of the idele entry is
  at most the local maximum entry (`MatrixInverseHeight.entry_le_localMaximum`).
  Multiplying the infinite-place bounds (with multiplicities) and the finite-place
  bounds (a `finprod` with finite support) gives the claim.
- `exists_characterNorm_le`: apply `closedImmersionAdelicHeightDomination` to `rho`
  and `sigma = χ.lineRepresentation`. This gives `C ≥ 1` and `e` with
  `characterNorm χ g ≤ C * adelicHeight rho g ^ e` for all `g`. For the inverse norm,
  apply the same bound at `g⁻¹` and use `adelicHeight_inv`.

### B. The height of a positive torus point is polynomial in its coordinates

Fix a splitting `e : T.toGrp ≅ splitTorus (ULift (Fin r))`, and write
`PositiveRealTorus.full F _ T e x` for the positive point with coordinates
`x : ULift (Fin r) → ℝ≥0ˣ`. Its coordinates are the same positive real at every
infinite place and `1` at every finite place.

- `positiveSize x = ∏ j, max (x j) (x j)⁻¹`, with the elementary facts
  `one_le_max_inv`, `one_le_positiveSize`, `le_positiveSize`, `positiveSize_inv`
  and `max_inv_pow_le`. The last says that if `y^n ≤ B` and `(y^n)⁻¹ ≤ B`, then
  `max(y, y⁻¹)^n ≤ B`.
- `adelicMatrix_diagonalTorus_full`: in the representation
  `e.hom ≫ GeneralLinear.diagonalTorus`, the positive point is the diagonal matrix of
  the positive scalar ideles `PositiveRealIdeles.full F (x k)`.
- `norm_diagonal_infinite_le` and `norm_diagonal_finite_le`: at an infinite place
  this diagonal matrix has sup norm at most `positiveSize x`; at a finite place it
  has sup norm at most `1`.
- `adelicHeight_diagonalTorus_full_le` (for `0 < r`): the diagonal height is at most
  `(r * positiveSize x) ^ [F:ℚ]`. The finite local factors are `1`. Each infinite
  local factor is at most `r * positiveSize x`, applying the same bound to `x⁻¹`
  through `positiveSize_inv`. The exponents sum to `[F:ℚ]` by
  `InfinitePlace.sum_mult_eq`.
- `adelicMatrix_map`: the adelic matrix of `rho` at the image of a point under a
  homomorphism `f` is that of `f ≫ rho`.
- `exists_adelicHeight_map_full_le`: there are `C ≥ 0` and `k` with
  `adelicHeight rho (i (full x)) ≤ C * positiveSize x ^ k`. For `r = 0` the only
  point is `1`. For `0 < r`, the diagonal representation of `T` is a closed embedding
  (`IsClosedSubgroup.of_iso` and `GeneralLinear.isClosedSubgroup_diagonalTorus`), so
  `closedImmersionAdelicHeightDomination` bounds the height of `i ≫ rho` by a power
  of the diagonal height. Then the previous lemma applies.

### C. Characters restricting to multiples of the coordinates

- `exists_characterNorm_full`: under `(characterRestrict i).range.FiniteIndex`, there
  is `m > 0`, namely the index, such that for every coordinate `j` some rational
  character `χ_j` of `G` satisfies
  `characterNorm F G χ_j (i (full x)) = x j ^ (m * [F:ℚ])` for all `x`. This holds
  because `m • (coordinate character j)` lies in the range
  (`AddSubgroup.nsmul_index_mem`). The norm of the coordinate character at `full x`
  is the normalized absolute value of `PositiveRealIdeles.full F (x j)`, namely
  `x j ^ [F:ℚ]`.

### D. The actual positive factor has trivial finite component

- `finite_positivePointMap`: for a split torus `T` and an intrinsic positive point
  `a`, `AdelicGroupPoints.finite F G (positivePointMap F G T i a) = 1`. The finite
  adelic point is determined by its evaluations (`affinePointEvaluation_injective`).
  Each evaluation is compared place by place: at every finite place the point is the
  image of the identity (`atFinitePlace_intrinsic`).

### The main theorem

Take `T`, `i` and `E` from the decomposition theorem, and the finite index from the
character-restriction theorem. Choose a splitting `e₀ : T.toGrp ≅ splitTorus I`,
renumber `I` as `ULift (Fin r)`, and let `e` be the resulting splitting. Obtain:

- `Cb, kb` from B;
- `m` and the characters `χ_j` from C;
- for each `j`, constants `C_j ≥ 1` and `ea_j` from A for `χ_j`.

Put `Cmax = ∑ C_j` and `emax = ∑ ea_j`. The theorem's constants are
`c = Cb * Cmax ^ (r * kb)` and `e = emax * r * kb`.

Given `g`, write `E⁻¹ g = (p₁, p₂)` and take `z = positivePointMap p₁`. Then
`g = z * p₂`. Properties 1–3 come from `positivePointMap_commute`, from D, and from
`z⁻¹ g = p₂ ∈ normOneSubgroup`. By `subgroup_eq_intrinsicSubgroup`, `p₁ = full x`
for some coordinates `x`.

For the height, write `H = adelicHeight rho g ≥ 1`. Since `p₂` is norm one,
`characterNorm χ_j g = characterNorm χ_j z = x j ^ (m * [F:ℚ])`. So A gives
`(x j ^ (m [F:ℚ]))^{±1} ≤ C_j H^{ea_j} ≤ Cmax H^{emax}`, and by `max_inv_pow_le`,
`max(x j, (x j)⁻¹) ^ (m [F:ℚ]) ≤ Cmax H^{emax}`. Taking the product over `j` gives
`positiveSize x ^ (m [F:ℚ]) ≤ (Cmax H^{emax})^r`. Finally,

```
adelicHeight rho z ≤ Cb * positiveSize x ^ kb
                   ≤ Cb * (positiveSize x ^ (m [F:ℚ])) ^ kb
                   ≤ Cb * ((Cmax H^{emax})^r) ^ kb
                   = Cb * Cmax^(r kb) * H^(emax r kb).
```

The second step uses `positiveSize x ≥ 1` and `m [F:ℚ] ≥ 1`.

## Relation to the statement's sketch

The statement's Markdown sketches a proof through the weight decomposition of
`rho ∘ i` and the determinant characters of the isotypic blocks. The implemented
proof avoids that decomposition. It bounds the central factor through any
characters whose restrictions are positive multiples of the coordinate characters,
which exist by the finite-index theorem. Each character norm is controlled through
its line representation and the published closed-embedding height domination,
applied twice: once on `G` for the characters, and once on `T` to compare `rho ∘ i`
with the diagonal representation.

## Checks

The development check reports zero errors and zero warnings. Inspection of
`centralNormOneHeightFactorStatement` shows only the axioms `propext`,
`Classical.choice` and `Quot.sound`. The module sets
`backward.isDefEq.respectTransparency false`.
