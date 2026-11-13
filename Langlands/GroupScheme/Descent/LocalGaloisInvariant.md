# Base-changed isomorphisms from local isomorphisms over a cover

Author: Worker 5375.

This internal module reuses the base-change isomorphism of
[`LocalGroupIsoBaseChangeRecovery`](../LocalGroupIsoBaseChangeRecovery.md).
When the local isomorphism is invariant under the Galois group, it descends
that isomorphism to the base field. It works for arbitrary schemes in one universe `u`,
with no characteristic or finiteness assumptions. The field section needs only `IsGalois`,
not finite dimensionality.

Notation: `b : S ⟶ B` is a morphism of schemes, `G₁` and `G₂` are group schemes over `B`,
and `e : LocalGroupIso G₁ G₂ (Over.mk b)` is a published local group isomorphism over the
cover `Over.mk b`. For a point `c : Z ⟶ Over.mk b`, `e.toFun c` is a group isomorphism
`(Z ⟶ G₁.X) ≃* (Z ⟶ G₂.X)`, natural in `Z` (`e.naturality`). The base change of a group
scheme `G` along `b` is `(Over.pullback b).mapGrp.obj G`. The published
`baseChangePointsEquiv b G T` identifies its points over `T : Over S` with the points of
`G` over `(Over.map b).obj T`, which is `T` regarded over `B`.

## Base-changed isomorphism (namespace `Langlands.GroupScheme.LocalGroupIso`)

- `baseChangeTestPoint (U := Over.mk b) T : (Over.map b).obj T ⟶ Over.mk b` is the
  published canonical cover point, with underlying morphism `T.hom`.
  - `map_comp_baseChangeTestPoint`: the published naturality theorem.
  - `testPoint_descent`: for an endomorphism `a : S ⟶ S` with `a ≫ b = b`, the published
    `descentTestIso b a ha T` followed by the canonical point of `(Over.map a).obj T` is
    the canonical point of `T` followed by `coverMap b a ha`.
- `coverMap b a ha : Over.mk b ⟶ Over.mk b` is `Over.homMk a ha`.
- `e.baseChangePoints T` is the published group isomorphism between the points over `T`
  of the two base changes. It conjugates the local equivalence at the canonical cover
  point by `baseChangePointsEquiv`. The published `baseChangePoints_project` and
  `baseChangePoints_naturality` give its projection formula and naturality.
- `e.toBaseChangeIso` is the published resulting isomorphism of base changes, built
  with `isoOfPoints`. `toBaseChangeIso_hom_points` states its effect on points.
- `IsInvariant b a ha` is the hypothesis
  `e.toFun (c ≫ coverMap b a ha) y = e.toFun c y` for every test scheme `Z`, cover point
  `c` and point `y`.
- `compatible_left`, `compatible_right` and `baseIso_compatible`: under `IsInvariant`,
  `e.toBaseChangeIso` commutes with the published descent identifications
  `descentBaseChangeIso b a ha`. The proof applies `hom_ext_points` and
  `baseChangePointsEquiv`. It then uses the published `baseChangePointsEquiv_descent`,
  `e.naturality`, `testPoint_descent` and invariance.
- `comp_eq_of_baseChange`: let `f : G₁ ⟶ G₂` be any homomorphism over `B` whose base
  change is `e.toBaseChangeIso.hom`. Then `y ≫ f = e.toFun c y` for every test scheme `Z`,
  cover point `c : Z ⟶ Over.mk b` and point `y : Z ⟶ G₁.X`. The proof regards `Z` as a
  scheme over `S` through `c.left` and compares the two canonical points.

## Galois descent (section `Galois`)

Here `K` and `M` are fields with `M/K` Galois, and `H₁`, `H₂` are group schemes over
`Spec K` with affine structure morphisms. `algebraBaseMap K M` and `galoisBaseMap K M σ`
are the published morphisms `Spec M → Spec K` and `Spec σ`.

- `galoisDescendIso e he : H₁ ≅ H₂` descends `e.toBaseChangeIso` with the published
  `Descent.GaloisHom.iso`, given invariance under `galoisBaseMap K M σ` for every
  `σ : M ≃ₐ[K] M`.
- `comp_galoisDescendIso_hom`: on every test scheme with a point of `Spec M`, the
  descended isomorphism agrees with the local isomorphism at that point.

## Provenance and scope

The provenance is internal. This is the standard Galois descent of a morphism defined
over a Galois cover and compatible with the Galois action. The module only connects the
published `LocalGroupIso`, `LocalGroupIso.toBaseChangeIso`, `descentBaseChangeIso` and
`Descent.GaloisHom.iso` interfaces. It does not need the pairwise independence
hypothesis of the published `LocalGroupIso.descend`: invariance under the translations by
`coverMap` is enough. It supplies the descent step of Task 6209
(`OuterTypeAHermitianPresentationStatement`).
