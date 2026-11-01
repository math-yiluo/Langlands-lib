# Extension of line bundles across arbitrary open immersions

`Langlands.AlgebraicGeometry.Picard.openImmersionLineBundleExtension.{u}`
proves exactly the published proposition
`Langlands.AlgebraicGeometry.Picard.OpenImmersionLineBundleExtensionStatement.{u}`.
The theorem has no outer hypotheses and retains arbitrary universe `u`.

For every locally Noetherian scheme `X`, every open immersion `j : Y ⟶ X`
whose structure-sheaf stalks are factorial outside the range of `j`, and every
actual line bundle `D` on `Y`, it produces an actual line bundle `E` on `X`
and an actual module-sheaf isomorphism

```text
((LineBundle.pullback j).obj E).obj ≅ D.obj.
```

This includes arbitrary open immersions and all source line bundles, with no
integrality, connectedness, separatedness, quasi-compactness, projectivity or
additional bundle condition. Factoriality is required only on the complement.
The published proposition and its imported definitions are unchanged.

The implemented proof composes four constructions by their Lean names.

1. `quasiAffineLineBundleIdealEmbedding` supplies an actual monomorphism from
   a line bundle into the structure module on a locally Noetherian
   quasi-affine scheme. Its proof takes a finite mono detector, chooses a
   section of the actual dual generating at that finite set, and evaluates
   that section on the original bundle.
2. `openImmersionInvertibleIdealExtension` extends such an actual invertible
   ideal across an open immersion with locally Noetherian target and factorial
   complementary stalks. It constructs the inverse-image ideal closure,
   proves its local rank one, and supplies an actual pullback isomorphism
   compatible with the monic inclusion.
3. `affineOpenImmersionLineBundleExtension_of_ideals` combines these two
   results for an affine target. Local Noetherianity makes the affine target
   Noetherian; its open source is Noetherian and quasi-affine. Thus the
   embedding result applies to the given bundle. The ideal-extension result
   then gives the actual extending bundle and pullback isomorphism required
   by `AffineOpenImmersionLineBundleExtensionStatement.{u}`.
4. `OpenImmersionLineBundleLocalToGlobal.of_affine` applies this proved affine
   statement to the general target. Affine extension followed by local
   trivialization produces compatible trivial charts near every target point.
   A fixed small family consisting of the original source chart and all
   trivial open charts admits a maximal strict atlas. Actual binary gluing
   preserves every selected transition when a compatible chart is added;
   maximality therefore makes the realized region all of `X`. Pullback along
   the inverse of its inclusion gives the extending bundle on `X`, and the
   distinguished original chart comparison gives exactly the displayed
   module-sheaf isomorphism.

The first two theorems discharge both explicit inputs of the affine adapter.
The resulting affine theorem discharges the sole input of the general
reduction. Consequently the final theorem has no residual conditional
extension premise. The two ideal proofs, affine adapter and local-to-global
reduction explain their own constructions in their paired Markdown; this
module only composes their exact interfaces and adds no external mathematical
assertion. The target's mathematical source is documented in its published
statement pair.

The proof uses none of
`DiscreteValuationRingSelfProductLineBundleExtensionStatement`,
`ValuationRingTwoAxisExtensionStatement`,
`ValuationRingAmpleExtensionStatement`,
`PicardZeroValuativeExtensionStatement` or
`RelativeDualSchemeValuativeExistenceStatement`, or results depending on those
conclusions.
