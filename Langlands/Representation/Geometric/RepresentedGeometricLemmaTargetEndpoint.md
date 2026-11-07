# Original inner target inducing covariance

This internal adapter identifies the full-intersection endpoint action of `RepresentedGeometricLemmaNormalizedCoefficient` with the normalized inducing covariance of the original inner target triple. The field and representation carrier have independent universes `u` and `v`. Every original represented parabolic map, the intersection datum, representative and specified `D.e` are retained.

Write `MI = pointImage (lQ ≫ q)`, `UJ = pointImage (r ≫ p)`, `PJ = pointImage p`,

```text
K  = MI ∩ z⁻¹ PJ z,
Rt = MI ∩ z⁻¹ UJ z.
```

`mem_targetParabolicPoints_leviPointsEquiv` and `mem_targetRadicalPoints_leviPointsEquiv` identify the original inner target parabolic and radical images under the original outer target Levi point equivalence. They specialize `mem_pointImage_leviPointsEquiv` using the exact `D.targetParabolicPoints_eq` and `D.targetRadicalPoints_eq` laws. These laws identify the original point images, rather than an auxiliary subgroup with merely the same abstract type.

`targetParabolicPointsEquiv` restricts `leviPointsEquiv q lQ hq hlQ` to the original `pointImage D.q'`, then removes the nested copy inside `MI`. This is a continuous group equivalence from that original parabolic point image onto the full literal `K`, retaining both subgroup topologies. Its underlying ambient point is exactly `rationalPoints.map (lQ ≫ q)` applied to the original parabolic point.

`originalTargetLeviProjection` is the original inner target semidirect projection, valued in `D.L'(k)` by the inverse of `leviPointsEquiv D.q' D.lQ' D.hq' D.hlQ'`. The affinity used by this point equivalence is derived from the original outer target Levi. `targetIntersectionLeviProjection_original` identifies the raw target projection through `targetParabolicPointsEquiv` with this exact original inner projection. The proof maps the original inner projection residual through `rationalPoints.map (lQ ≫ q)`, identifies its radical image using `D.targetRadicalPoints_eq`, and applies uniqueness of the original raw semidirect projection. These point membership and projection theorems omit field Hausdorffness and ambient local compactness and nonarchimedean assumptions.

For the Haar comparison, the field topology is Hausdorff and the ambient group has its canonical locally compact nonarchimedean rational-point topology. `targetEndpointHalfCharacter_transport` compares the full target half, rather than only its common-Levi restriction. It first applies `GroupTransport.closedHalfCharacter_transport` to the original outer Levi equivalence, using the two exact membership laws above. It then applies `closedHalfCharacter_subgroupOf` to remove the nested radical and acting group inside the closed outer target Levi image. Thus the positive Haar half of the original inner target radical on the original `pointImage D.q'` equals the full literal endpoint half on `K` at the same original point. Affinity, topology, local compactness and the nonarchimedean-group instance for the original target Levi are derived from its represented triple. No dynamic realization, relative-root input or modulus identity is assumed for these transport results.

Let `A` be any smooth complex representation of the original `M(k)`, and let `S = pointImage (D.r' ≫ D.p')`. `originalTargetInducingCoefficient` is an action on precisely

```text
Jacquet.Localization.Coinvariants A.representation S 1.
```

Its definition uses the published actual `inducingRepresentation` for the original inner target triple `D.q', D.lQ', D.rQ'`. The input is the actual original normalized inner source Jacquet object, pulled through the specified `D.e`, then transported from `D.L'(k)` to its original inner target Levi image. This is exactly the covariance coefficient used by the represented normalized target induction; it does not yet construct any space of induced functions.

`originalTargetInducingCoefficient_eq_endpoint` proves equality with `originalTargetIntersectionEndpointAction` pulled back through `targetParabolicPointsEquiv`. Extensionality reduces this to original source vector classes. The full target half comparison and the original projection identity give equality of the two scalar actions on the same original quotient classes. Source and target ambient Levi instances used in the actual functors are derived from their original represented triples.

Finally, over a nonarchimedean local field with smooth affine ambient group, `originalTargetInducingCoefficientEquiv` compares the earlier scalar-normalized full-intersection coefficient, pulled to the original target parabolic image, with this actual original inducing covariance. It retains the supplied simultaneous dynamic realization, the relative-root-system input for the actual transported common torus and injectivity of algebraic-character restriction to `D.targetCommonTorusHom`. The common torus closed immersion comes from the datum's ambient maximal-split-torus law. The preceding conditional coefficient cancellation and unconditional endpoint transport give equality of actions; `equivOfRepresentationEq` packages it as an identity linear equivalence. The `…_mk` and `…_natural` theorems state that it preserves every original vector class and commutes with the quotient maps from every morphism of arbitrary smooth source representations in universe `v`.

The provenance is internal: this combines the six original point identities, existing point-image and subgroup equivalences, original semidirect projection uniqueness, actual Haar-character transport, the published original normalized source and target functors and the preceding conditional coefficient calculation. It makes no new external-source assertion. Identification of the coefficient produced by the actual compact-quotient integral, compact induction and function-space comparisons, discharge of the retained dynamic/root/detection inputs and the exact closed orbit-comparison isomorphism remain outstanding. The published closed target and its hypotheses are unchanged.
