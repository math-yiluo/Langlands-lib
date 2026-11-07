# Forward Haar factors on the original represented common Levi

This internal adapter defines five actual forward Haar moduli on all rational points of the original target common Levi `D.L'` of a `GeometricLemmaIntersectionDatum`. It then specializes the full common-centralizer Haar balance to those moduli. It uses the original datum, representative, torus and subgroup maps throughout.

Write `MI = pointImage (lQ ≫ q)`, `MJ = pointImage (l ≫ p)`, `UI = pointImage (rQ ≫ q)`, `UJ = pointImage (r ≫ p)` and `n = z⁻¹`. The five moduli are pulled back through `D.targetCommonLeviPointsEquiv`, whose underlying ambient point is the original map `D.lQ' ≫ D.q' ≫ lQ ≫ q`. Their subgroups in the original ambient rational-point group are:

| Declaration | Actual subgroup |
| --- | --- |
| `forwardTargetRadicalModulus` | `UI` |
| `forwardSourceRadicalModulus` | `n UJ n⁻¹` |
| `forwardSourceEndpointModulus` | `UI ∩ n MJ n⁻¹` |
| `forwardTargetEndpointModulus` | `MI ∩ n UJ n⁻¹` |
| `forwardIntersectionModulus` | `UI ∩ n UJ n⁻¹` |

Every factor is the Haar character of forward conjugation by the same original common-Levi point. In particular, the two endpoint subgroups are distinct intersections. The source endpoint is the inverse conjugate of the original `D.N'`, and the target endpoint is the original `D.U'`, by the full subgroup-functor equalities in `RepresentedGeometricLemmaHaarModels`.

For a supplied `R : D.DynamicRealization`, write `χ` and `ψ` for its target and source cocharacters followed by the original transported torus map to `G`. The five `haar…Points_eq` lemmas identify the rational-point subgroups of `Uχ`, `Uψ`, `Uχ ∩ Zψ`, `Uψ ∩ Zχ`, and `Uχ ∩ Uψ` with the five subgroups in the table, in that order. The endpoint with reversed intersection order uses commutativity of subgroup intersection; it does not identify the two Levi centralizers. Closedness follows from the original radical and Levi closed embeddings, conjugation and intersection.

The five `haar…Character_eq_forward` lemmas identify the dynamic forward Haar characters with the five defined moduli as entire monoid homomorphisms on `D.L'(k)`. The proof compares equal point subgroups and the same ambient normalizer point. Proof irrelevance handles their closedness witnesses. Thus this step changes neither the acting group nor the point at which the character is evaluated, and needs no character-detection premise.

Over a nonarchimedean local field with smooth affine ambient `G`, `forwardHaarCharacter_product_square` gives

```text
δtarget · δsource = δsourceEndpoint · δtargetEndpoint · δintersection².
```

Its explicit inputs are the supplied `R`, a relative-root system for the original transported ambient torus, and injectivity of `characterRestrict D.targetCommonTorusHom`. The proof applies `centralizingHaarCharacter_product_square_of_characterRestrict_injective` using the original five represented subgroup models from HaarModels and `Lie.finiteCoordinates` on each actual Lie kernel, then rewrites by the five character comparisons. The finite-type and affine instances follow from ambient smoothness and the established closed embeddings. Hausdorffness of the ambient point group follows from affinity and `T2Space k`.

The definitions `forwardSourceCorrectionCharacter` and `forwardTargetCorrectionCharacter` are respectively

```text
sqrt(δsource) · sqrt(δtargetEndpoint)⁻¹ · sqrt(δintersection)⁻¹,
sqrt(δtarget) · sqrt(δsourceEndpoint)⁻¹ · sqrt(δintersection)⁻¹,
```

with the positive unit square roots embedded into complex units. `forwardCorrectionCharacter_product_eq_one` proves their product is the trivial character under the same explicit inputs. It specializes the generic full-Haar correction-product theorem with those original models and applies the same five character equalities.

The constructions and proofs are derived from the published datum, the literal point-intersection and forward-modulus APIs, the supplied simultaneous dynamic realization, and the full common-centralizer Haar-balance theorem. They make no new external-source assertion. This module does not prove existence of `R`, the relative-root system, or character detection. It also does not yet identify these factorized correction expressions with the original epsilon corrections, or construct the natural representation isomorphism. The exact closed `RepresentedGeometricLemmaOrbitComparisonStatement.{u,v}` is unchanged and remains a separate proof obligation.
