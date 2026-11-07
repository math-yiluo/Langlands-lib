# Normalized coefficient on the actual source Jacquet quotient

This internal adapter transfers the scalar equality of `RepresentedGeometricLemmaCharacterInflation` to two actions on the same actual source-intersection Jacquet quotient. The field and representation carrier have independent universes `u` and `v`. The source is an arbitrary smooth complex representation `A` of the original represented source Levi's own rational points. No admissibility, finite length or irreducibility condition is used.

Let `S = pointImage (D.r' ≫ D.p')`, a subgroup of the original `M(k)`. Every action in this module has the same carrier

```text
Jacquet.Localization.Coinvariants A.representation S 1.
```

These are the original trivial-character coinvariant classes, rather than an abstractly isomorphic replacement. `ordinaryCommonLeviCoefficientAction` is the published ordinary localized quotient action of the original source common Levi image, pulled back through the actual map

```text
D.L'(k) --D.e--> D.M'(k) --D.l' ≫ D.p'--> M(k).
```

The second map is range-restricted to its actual source Levi image. No ambient topology comparison is needed to define that point homomorphism.

Write `K = pointImage (lQ ≫ q) ∩ z⁻¹ pointImage p z`. The definition `normalizedTargetIntersectionCoefficientAction` pulls the ordinary common-Levi action to `K` through `targetIntersectionLeviProjection` and twists by the exact full-intersection coefficient character of `CharacterInflation`.

`originalTargetIntersectionEndpointAction` uses the actual normalized `leviJacquetFunctor` of the original inner source triple `D.p', D.l', D.r'`. It pulls that action through `D.e` and the same original target projection, then twists by the full target endpoint half-character of the literal radical `pointImage (lQ ≫ q) ∩ z⁻¹ pointImage (r ≫ p) z` on the whole group `K`. The source ambient affinity, canonical topology, local compactness and nonarchimedean-group instances used by this normalized functor are derived from the original source triple. They are not supplied extra hypotheses.

`normalizedSourceJacquetAction_eq` unfolds the actual original normalized source Jacquet action and rewrites its inverse half using `sourceInverseHalfCharacter_commonLevi`. It identifies that action, pulled through `D.e`, with the inverse source-endpoint half twist of `ordinaryCommonLeviCoefficientAction`. `originalTargetIntersectionEndpointAction_eq` then commutes twisting with the original target projection and combines both endpoint twists. This gives precisely the endpoint-character twist of the ordinary source quotient action on `K`. These two action identities require the original Hausdorff field and canonical locally compact nonarchimedean ambient rational-point topology; they use no dynamic realization, root or character-detection premise.

For a nonarchimedean local field, supplied simultaneous `R : D.DynamicRealization` and ambient second countability, `normalizedTargetIntersectionCoefficientAction_eq_epsilonTwist` rewrites the earlier full character factorization. The normalized coefficient action is the original endpoint action twisted by the product of both original epsilon corrections, inflated through the original target projection. This retains the discrepancy rather than assuming a modulus equality.

With smooth affine ambient group, `normalizedTargetIntersectionCoefficientAction_eq_endpoints` retains the relative-root-system premise on the actual transported common torus and injectivity of algebraic-character restriction to `D.targetCommonTorusHom`. It applies the existing full-intersection scalar cancellation and obtains equality of the two actions on every original quotient class. The torus closed immersion is derived from its existing ambient maximal-split-torus law.

`normalizedTargetIntersectionCoefficientEquiv` packages that equality as an actual `Representation.Equiv` with underlying linear equivalence the identity. Its `…_mk` theorem records that it sends every original vector class to the same vector class. `…_natural` states and proves that it commutes with the published quotient map induced by every morphism between arbitrary smooth source representations in universe `v`; the underlying equality is definitional because the equivalence is the identity. Thus this is a natural coefficient-level comparison, with independent field and carrier universes.

The provenance is internal: the module combines the original represented normalized source Jacquet functor and its previously proved endpoint character, the actual ordinary quotient action, the original `D.e` and target projection, character-twist algebra and the full-intersection scalar equality. It does not identify the coefficient produced by the actual compact-quotient integral with this coefficient action, compare compactly induced representations, identify the full target endpoint with the original inner target inducing covariance after its required point-group transport, construct the natural orbit-comparison isomorphism, or discharge the retained dynamic, root and character-detection inputs. The exact closed target and its hypotheses are unchanged.
