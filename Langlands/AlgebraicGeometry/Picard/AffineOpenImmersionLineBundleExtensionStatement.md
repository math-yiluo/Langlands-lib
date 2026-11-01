# Line-bundle extension with affine target

`Langlands.AlgebraicGeometry.Picard.AffineOpenImmersionLineBundleExtensionStatement.{u}`
is the affine-target specialization of the published general
`OpenImmersionLineBundleExtensionStatement`. It quantifies over locally
Noetherian affine schemes `X`, arbitrary schemes `Y`, and open immersions
`j : Y ⟶ X`. Assuming factorial structure-sheaf stalks only at points outside
`Set.range j`, every actual Library line bundle `D` on `Y` must be the
pullback of an actual line bundle `E` on `X`, up to an actual module-sheaf
isomorphism `((LineBundle.pullback j).obj E).obj ≅ D.obj`.

This is a derived interface: specialize the general statement by adding
`[IsAffine X]`. The source proof of Stacks Project Lemma 31.29.3, Tag
[0BD9](https://stacks.math.columbia.edu/tag/0BD9), first proves this affine
case before gluing and maximal extension. The interface is intended to
separate that local construction from arbitrary locally Noetherian targets.
It supplies only the proposition, without a proof or new axiom.

The source's affine argument represents the given bundle by an effective
Cartier divisor on `Y` (which is Noetherian and quasi-affine), then extends
the divisor using Tag 0BD8. In the invertible-ideal convention, the separate
`QuasiAffineLineBundleIdealEmbeddingStatement` and
`OpenImmersionInvertibleIdealExtensionStatement` are the two sufficient
inputs. Neither is assumed as an outer hypothesis of this proposition.
No integrality, reducedness, connectedness, projectivity, or restriction
on the given bundle is imposed. Affineness is an extra hypothesis only
for this local interface; the general task retains arbitrary targets.

The retained source is `stacks-open-line-bundle-extension-0bd9-2026-11-01`,
directory SHA256
`e04f95facf97c45df0e888af89a8d92fd61988dcb397e6354110b6e4d184380d`,
at `/home/taskhub/pilot/literature/Stacks Project - Open line-bundle extension and Cartier divisors, Tags 0BD9, 0BD8, 0AYM (HTML snapshot 2026-11-01)`.
The complete statement, proof and comments of `0BD9.html` were read in the
parent task. No corresponding errata file was found in bounded Library,
private and project notes filename searches.
