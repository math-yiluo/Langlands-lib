# Compact target induction and the original represented piece

This internal construction supplies the target function-space adapter for an arbitrary represented intersection datum `D`. It compares actual compact induction of the normalized literal target-intersection coefficient with the original datum's `pieceFunctor`. The field and source representation carrier have independent universes `u` and `v`. Every original represented map, the representative `z`, the specified conjugation `D.e` and the original ordinary source Jacquet quotient are retained.

Write

```text
MI = pointImage (lQ ≫ q),
K  = MI ∩ z⁻¹ (pointImage p) z,
Ki = K.subgroupOf MI,
S  = pointImage (D.r' ≫ D.p').
```

All ambient rational-point groups have their canonical topology. The original source and target Levi groups use `leviPointTopology` for their original represented maps.

`targetParabolicQuotientHomeomorph` identifies the actual original quotient `pointImage D.q' \ L(k)` with `Ki \ MI`. The proof applies quotient congruence to the original continuous group equivalence `leviPointsEquiv q lQ hq hlQ`. Compatibility with the right-coset relation follows from the established original point-membership identity at `y * x⁻¹`. Consequently, `targetIntersectionQuotient_compactSpace` transfers a supplied compactness instance for the actual original target quotient to the literal intersection quotient. It omits field Hausdorffness and ambient local compactness and nonarchimedean assumptions. This transfer does not prove the original quotient compact.

For any smooth complex source representation `A`, `targetIntersectionCoefficientInLevi` is the preceding `normalizedTargetIntersectionCoefficientAction A`, restricted through the canonical equivalence from `Ki` to the full literal `K`. Its carrier is exactly

```text
Jacquet.Localization.Coinvariants A.representation S 1.
```

In particular, it retains the earlier scalar normalization on the full intersection, including the distinct radical Haar moduli. `targetIntersectionCoefficientMap` has underlying linear map `Jacquet.Localization.mapLinear S 1 (SmoothRep.hom f)` for every source morphism `f`. The original source Jacquet intertwiner gives equivariance before twisting; `twistIntertwining` retains that quotient map after the same full scalar twist and target projection. The quotient-class formulas prove identity and composition, giving `normalizedTargetIntersectionCoefficientFunctor` on the full smooth source category.

`targetNormalizedCompactFunctor` applies actual `compactInductionFunctor Ki` to this coefficient functor, pulls the resulting smooth representation back through the original outer target Levi point equivalence, and forgets only its smoothness proof. Its target is `Rep.{max u v} ℂ (rationalPoints L)`, matching the original `D.pieceFunctor`. No admissibility, finite-length or irreducibility condition occurs.

The comparison constructions are over a nonarchimedean local field with smooth affine ambient group. They explicitly retain a simultaneous `R : D.DynamicRealization`, `HasRelativeRootSystem` for the actual transported common torus, injectivity of algebraic-character restriction to `D.targetCommonTorusHom`, and compactness of the actual quotient `pointImage D.q' \ L(k)`. The common torus closed immersion is derived from the datum's ambient maximal-split-torus law. These are intermediate inputs, not extra premises added to the published closed orbit-comparison statement.

`targetNormalizedInductionEquiv` first uses the preceding conditional equality of normalized full-intersection and endpoint actions, followed by the unconditional original target covariance identity. Thus the coefficient transported to `pointImage D.q'` equals `originalTargetInducingCoefficient A`, the exact covariance in the original normalized inner target induction. There is no change of the original source quotient carrier.

The supplied actual quotient compactness transfers to `Ki \ MI`. The canonical inclusion from compact induction to smooth induction is then bijective: the projected support of every smooth induced function is closed in this compact quotient. Its representation equivalence is restricted along the original outer target Levi map. Finally, `precomposeSmoothInducedGroupEquiv` transports the whole smooth induced function and its uniform open right stabilizer through that same original point equivalence and its restriction to the original parabolic. Its resulting representation is definitionally the object of `D.pieceFunctor`.

The forward map has the concrete formula recorded by `targetNormalizedInductionEquiv_eval`:

```text
(E_A F)(x) = F(leviPointsEquiv q lQ hq hlQ x).
```

Here the value on both sides is the same original source Jacquet quotient class. The inverse precomposes with the inverse point equivalence and supplies compact support using the compact quotient. `targetNormalizedInductionEquiv_natural` compares the full functions for every source morphism: applying `compactInducedMap` to the original quotient map before the equivalence equals applying the actual `D.pieceFunctor.map f` afterwards. Extensionality reduces this to the same quotient map at every original target point. `targetNormalizedCompactIso` packages these component representation equivalences and their naturality as an isomorphism of functors to the original represented piece.

The provenance is internal: the original represented point-membership identities, quotient congruence, the actual original source Jacquet quotient maps, the preceding full coefficient cancellation and original target inducing covariance identity, the compact-quotient inclusion theorem and continuous group transport prove this adapter. It makes no new external-source assertion. The actual compact-integral orbit comparison on the source side, identification of its coefficient with this normalized coefficient, and discharge of all retained structural and quotient-compactness inputs remain outstanding. This contribution does not prove the exact closed represented orbit-comparison proposition or modify its published pair or imported closure.
