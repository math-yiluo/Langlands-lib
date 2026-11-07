# Original epsilon corrections on the represented common Levi

This internal adapter identifies both original geometric-lemma epsilon corrections with their factorized forward characters on all rational points of the original target common Levi `D.L'`. The datum, representative, common Levi and ambient point maps are those of `GeometricLemmaIntersectionDatum`. The field has universe `u`; no representation-carrier universe or representation-finiteness premise occurs.

Write `PI = pointImage q`, `PJ = pointImage p`, `MI = pointImage (lQ ≫ q)`, `MJ = pointImage (l ≫ p)`, `UI = pointImage (rQ ≫ q)`, `UJ = pointImage (r ≫ p)` and `n = z⁻¹`. Both `originalSourceCorrectionCharacter` and `originalTargetCorrectionCharacter` are the existing generic correction characters pulled back through `D.targetCommonLeviPointsEquiv`. Its underlying ambient point map is `D.lQ' ≫ D.q' ≫ lQ ≫ q`. Thus both characters have the same original acting group and evaluate at the same common-Levi point.

All subsequent proofs retain a supplied `R : D.DynamicRealization`. The first two lemmas establish that the original target projection preserves `n UJ n⁻¹`, and that the original source projection for the actual conjugated triple with parabolic inclusion `p ≫ Iso.hom (G.innerIso n)` preserves `UI`. They use the six subgroup identities in `R` to apply `projection_mem_commonTorusUnipotent`. That helper identifies the original projection with the dynamic limit and applies closed-stable limit membership to the second dynamic unipotent subgroup of the same torus. These projection statements need ambient affinity, but omit field Hausdorffness, local compactness and the nonarchimedean-group premise.

For the Haar comparisons the field topology is Hausdorff, the ambient rational-point group has its canonical locally compact nonarchimedean topology, and that group is second countable. All subgroup closedness and normalizer conditions are derived from the original parabolics, Levis and radicals. Continuity of the original projections comes from `continuous_projection_pointImage`; it is not a supplied extra modulus or projection-preservation assumption.

The source correction intersection, after the existing forward-conjugation transport, is `PI ∩ n UJ n⁻¹`. Its two semidirect factors are `MI ∩ n UJ n⁻¹` and `UI ∩ n UJ n⁻¹`. Applying `interOfProjection_closedRestrictCharacter` to the original target decomposition proves `originalSourceCorrectionIntersectionModulus_eq_mul`: its modulus is `D.forwardTargetEndpointModulus * D.forwardIntersectionModulus`.

The target correction intersection is `UI ∩ n PJ n⁻¹`. Applying the same theorem to the actual conjugated source decomposition gives factors `UI ∩ n MJ n⁻¹` and `UI ∩ n UJ n⁻¹`. The proof uses `rationalPoints_range_comp_innerIso` for each member of that triple and reorders subgroup intersections. It retains the original common-Levi acting point throughout. This proves `originalTargetCorrectionIntersectionModulus_eq_mul`, whose product is `D.forwardSourceEndpointModulus * D.forwardIntersectionModulus`.

The two `original…CorrectionCharacter_eq_forward` theorems combine those literal modulus products with the existing generic correction formulas and source-radical conjugation transport. Multiplicativity of the canonical positive unit square root gives the full character identities

```text
originalSourceCorrectionCharacter
  = sqrt(δsource) · sqrt(δtargetEndpoint)⁻¹ · sqrt(δintersection)⁻¹,
originalTargetCorrectionCharacter
  = sqrt(δtarget) · sqrt(δsourceEndpoint)⁻¹ · sqrt(δintersection)⁻¹.
```

Here each positive square root is embedded into complex units, and the five `δ` characters are exactly the forward moduli of `RepresentedGeometricLemmaHaarBalance`. The two endpoint intersections remain distinct. Both equalities hold on the entire original common Levi; they do not use restriction to the torus or character detection.

Finally, over a nonarchimedean local field with smooth affine ambient group, `originalCorrectionCharacter_product_eq_one` proves that the product of the two original characters is the trivial character. Besides `R`, it explicitly assumes `HasRelativeRootSystem` for the original transported ambient torus and injectivity of `characterRestrict D.targetCommonTorusHom`. The closed-immersion instance for that torus comes from its existing ambient maximal-split-torus law. The proof obtains ambient second countability from `RationalPointFamily.rationalPoint_secondCountable`, rewrites by the two full character identities, and applies the existing conditional forward correction-product theorem.

The provenance is internal: the construction combines the published intersection datum, generic correction-character transport, original projection continuity, dynamic-limit preservation, semidirect Haar factorization and full common-centralizer balance. It makes no additional external-source assertion. Existence of the supplied dynamic realization, the relative-root result and character detection remain explicit obligations. The module does not construct the natural representation isomorphism or prove the exact closed `RepresentedGeometricLemmaOrbitComparisonStatement.{u,v}`, whose published statement and hypotheses are unchanged.
