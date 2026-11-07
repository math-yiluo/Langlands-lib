# Character inflation on the full represented target intersection

This internal adapter extends the scalar comparison from every point of the original common Levi to every point of the full literal target intersection. It uses the unchanged `GeometricLemmaIntersectionDatum`, the same representative and the same original point maps. The field has universe `u`; no representation carrier or finiteness condition occurs.

Write `MI = pointImage (lQ ≫ q)`, `MJ = pointImage (l ≫ p)`, `UI = pointImage (rQ ≫ q)`, `UJ = pointImage (r ≫ p)` and `PJ = pointImage p`. All groups below are literal subgroups of the original ambient rational-point group:

```text
K  = MI ∩ z⁻¹ PJ z,
Lt = MI ∩ z⁻¹ MJ z,
Rt = MI ∩ z⁻¹ UJ z,
C  = UI ∩ z⁻¹ PJ z.
```

The supplied datum already proves the semidirect decomposition `K = Lt ⋉ Rt` through `targetPoints_isSemidirectDecomposition`. `targetCommonLeviInIntersection` is the original `D.targetLeviPointsEquiv` followed by the inclusion `Lt → K`. `targetIntersectionLeviProjection` is that same semidirect projection, followed by `D.targetLeviPointsEquiv.symm`, so its codomain is the original `D.L'(k)`. The projection on the common-Levi inclusion is the identity.

The ambient group has its canonical locally compact nonarchimedean topology, and the field topology is Hausdorff. `targetIntersectionRadicalModulus` is the original closed target-radical conjugation modulus, restricted to `K`; normalization follows from `K ≤ MI`. `targetIntersectionCorrectionModulus` is the modulus of the full original subgroup `C`, again at the same point of `K`; normalization follows by intersecting the target-radical and conjugated source-parabolic normalizers. Closedness is derived from the original represented triples.

The two `…Modulus_commonLevi` theorems identify restrictions with the actual original target radical and full original target correction-intersection moduli of the preceding common-Levi calculation. For the latter, `geometricTargetCorrectionIntersectionModulus_eq_ambient` compares the original correction-subgroup presentation with the literal subgroup `C` at equal ambient acting points.

Denote those full-intersection moduli by `U_K` and `D_K`, and the original common-Levi source radical modulus by `V`. The definition `normalizedTargetIntersectionCoefficientCharacter` is

```text
η_K = sqrt(U_K) / D_K · (sqrt(V) ∘ π),
```

where `π` is the original target projection just defined. The denominator is the full modulus, without a square root. `normalizedTargetIntersectionEndpointCharacter` is

```text
ζ_K = half(Rt on K) · (inverseHalf(source endpoint) ∘ π).
```

Here `half(Rt on K)` is the actual closed-subgroup Haar half-character of `Rt` on the whole group `K`, rather than merely its restriction to `Lt`. Both characters restrict to the corresponding original common-Levi characters. The common-Levi endpoint factors were identified with the actual inner target inducing half and the `D.e`-transported actual inner source Jacquet inverse half in `RepresentedGeometricLemmaNormalizedCharacter`.

`targetIntersectionCharacter_eq_projection` gives the elementary inflation criterion for any group-valued character of `K` trivial on `Rt`. For each `x`, the element `s(π(x))⁻¹ x` belongs to `Rt` by the original semidirect decomposition. Applying the character to this element gives the factorization through `π`. This algebraic criterion and the projection-on-inclusion identity omit field Hausdorffness and ambient local compactness and nonarchimedean assumptions.

The remaining inflation theorems additionally assume a nonarchimedean local field. `targetIntersectionRadical_isLimitOfCompactSubgroups` uses the exact original equality

```text
Rt = pointImage (D.rQ' ≫ D.q' ≫ lQ ≫ q).
```

Applying `isLimitOfCompactSubgroups_pointImage_radical` to the represented radical `D.rQ'` and the closed composite `D.q' ≫ lQ ≫ q` proves compact-subgroup containment directly. No dynamic realization, standardness or root presentation is needed for this step. Closed intersection transfers that property to the literal copy of `Rt` inside `K`.

Both `U_K` and `D_K` have open kernels. `positiveCharacter_eq_one_on_compactLimit` makes them trivial on `Rt`, and the source half is trivial there because the original projection equals one. This proves `normalizedTargetIntersectionCoefficientCharacter_eq_one_on_radical`, then the algebraic criterion and the restriction identity prove `normalizedTargetIntersectionCoefficientCharacter_eq_projection`.

For the endpoint character, compact-subgroup containment gives unimodularity of the original `Rt`. `closedHalfCharacter_eq_comp_projection` expresses the full target half as its Levi restriction through the original projection. This half and the source endpoint factor are therefore trivial on `Rt`. Applying the same criterion proves `normalizedTargetIntersectionEndpointCharacter_eq_projection`.

With a supplied simultaneous `R : D.DynamicRealization` and ambient second countability, `normalizedTargetIntersectionCoefficientCharacter_eq_epsilonEndpoints` transfers the earlier common-Levi factorization to the whole literal intersection:

```text
η_K = ((originalSourceCorrectionCharacter · originalTargetCorrectionCharacter) ∘ π) · ζ_K.
```

Finally, with smooth affine ambient group, `normalizedTargetIntersectionCoefficientCharacter_eq_endpoints` retains the relative-root-system input for the actual transported common torus and injectivity of algebraic-character restriction to `D.targetCommonTorusHom`. The torus closed immersion comes from its original ambient maximal-split-torus law. The earlier conditional common-Levi cancellation and both inflation identities give `η_K = ζ_K` on every point of `K`.

The provenance is internal: this combines the original six intersection point equalities and semidirect decomposition, actual closed-subgroup Haar characters, the published represented-radical compact-limit theorem, positive-character triviality and the preceding scalar calculation. It follows the elementary inflation pattern of `RationalGeometricNormalizedCoefficientInflation` without its standard-parabolic interface. It does not identify this scalar expression with the Haar ratio or action of the compact-quotient integral, construct a natural representation isomorphism, discharge the retained dynamic, root and character-detection inputs, or prove the exact closed orbit-comparison target. The published target and its hypotheses are unchanged.
