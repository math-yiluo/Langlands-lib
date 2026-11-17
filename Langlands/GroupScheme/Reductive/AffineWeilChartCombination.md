# Combining Weil-restriction presentations on finitely many charts

Namespace `Langlands.GroupScheme.AffineWeil.ChartCombination`. This internal construction
combines Weil-restriction presentations of a group on finitely many affine charts into one
presentation on the product chart. All rings and index types lie in one universe `u`. It is
used by `Langlands.GroupScheme.affineWeilPairEtaleDescent_of_singleChart` to reduce étale pair
descent along a covering family to descent along one étale cover.

## Product rings and coefficient algebras

Fix a finite index type `I`, commutative rings `R i`, and `R i`-algebras `B i`.

- `evalAlgebra R i` makes `R i` an algebra over `∀ j, R j` through evaluation at `i`.
  `factorAlgebra R B i` makes `B i` an algebra over `∀ j, R j` through the same evaluation
  (`Algebra.compHom`). `coefficientAlgebra R B` is the resulting componentwise algebra
  structure of `∀ j, B j` over `∀ j, R j`. Using `Algebra.compHom` keeps its scalar action
  definitionally equal to Mathlib's componentwise `Pi.module'`. `coefficient_smul_apply`
  records `(r • c) i = r i • c i`.
- `isLocalization_away` shows that evaluation `∀ j, R j → R i` is the localization away from
  the idempotent `Pi.single i 1`. Hence `R i` is étale over the product.
- If every `B i` is finite (resp. étale) over `R i`, then `∀ j, B j` is finite
  (`coefficient_finite`) and étale (`coefficient_etale`) over `∀ j, R j`. It is finitely
  presented and flat, hence projective (`coefficient_projective`).

## The assembled coefficient group

`component B i` is the open immersion `Spec (B i) → Spec (∀ j, B j)`, the spectrum of
evaluation. These maps form a coproduct decomposition (Mathlib's `sigmaSpec`). Given group
schemes `H i` over `Spec (B i)`, `group B H` is the group scheme over `Spec (∀ j, B j)` assembled
with Worker 632's `Descent.DisjointGroupAssembly.group`. Its restriction to each component is
`H i` (`componentIso`), and its underlying scheme is the disjoint union (`underlyingIso`). It is
affine and locally of finite type when the `H i` are. `smooth`, `isReductive` and
`isAlmostSimple_geometricFiber` transfer smoothness, reductivity and almost simple geometric
fibres from the `H i`. `geometricFiber_property` handles any field-group property invariant
under isomorphism and reflected by field extension. It uses
`RelativeLevi.geometricFiberBaseChangeIso` at a point of a component.
These proofs adapt the proofs Worker 632 gave for `AffineWeil.FiniteFamily` (copies of one base
ring) to a family of different rings.

## Factor tensor products

Let `T` be an `R i`-algebra with a compatible algebra structure over `∀ j, R j`
(`[IsScalarTower (∀ j, R j) (R i) T]`). For example, take `testAlgebra R i T`, evaluation
followed by the `R i`-action, with `testAlgebra_isScalarTower`. Then
`tensorFactorEquiv R B i T : (∀ j, B j) ⊗[∀ j, R j] T ≃ₐ[∀ j, B j] B i ⊗[R i] T` sends
`c ⊗ t` to `c i ⊗ t`. Here `B i ⊗[R i] T` is an algebra over `∀ j, B j` through evaluation
(`factorTensorAlgebra`). The forward map `toFactor` is `Algebra.TensorProduct.lift`. The
inverse `fromFactor` is the additive map `b ⊗ t ↦ Pi.single i b ⊗ t`, and the two maps are
mutually inverse on pure tensors. This uses that `Pi.single i 1` acts as `1` on `T`.
`tensorFactorEquiv_naturality` gives naturality in `T`.

## Weil restriction over the product chart

`weil R B H` is `AffineWeil.groupScheme (∀ j, R j) (∀ j, B j) (group B H)`, for finite,
projective, étale `B i` and affine, locally finite type `H i`.

For a test algebra `X` over `R i`, `factorPointsEquiv R B H i X` identifies the points of the
restriction of `weil R B H` to `Spec (R i)` (along `component R i`) with the points of
`AffineWeil.groupScheme (R i) (B i) (H i)`. It composes the following equivalences:

1. the affine base-change point equivalence `affinePointsBaseChangeMulEquiv`;
2. the Weil point equivalence `AffineWeil.pointsEquiv` over the product;
3. the factor tensor isomorphism `tensorFactorEquiv` (through `affinePointsAlgEquiv`);
4. the affine base-change point equivalence along `component B i`;
5. the component isomorphism `componentIso` (through `affinePointsIsoEquiv`);
6. the inverse Weil point equivalence over `R i`.

The general form `factorPointsEquivOf` takes any compatible structure on the test algebra, and
`factorPointsEquivOf_naturality` proves naturality step by step from the published naturality
lemmas. `factorAffinePointIso` is the natural isomorphism of affine point functors.
`factorIso` is the resulting group-scheme isomorphism, obtained with
`AffinePointComparison.iso`.

## Combination

Let `G` be a group scheme over `Spec A` and let the `R i` be `A`-algebras, so that `∀ j, R j`
carries Mathlib's product algebra structure. `component_comp_baseMap` identifies each component
followed by the product structure map with the structure map of `R i`.
`componentBaseChangeIso` identifies the restriction of `G_{∏ R}` to `Spec (R i)` with `G_{R i}`.
`surjective_baseMap` shows that `Spec (∀ j, R j) → Spec A` is surjective when the images of
the `Spec (R i)` cover `Spec A`.

Given isomorphisms `φ i : G_{R i} ≅ AffineWeil.groupScheme (R i) (B i) (H i)`,
`combinedIso R B H G φ : G_{∏ R} ≅ weil R B H` is assembled with
`Descent.DisjointComponents.groupIso` from the component isomorphisms
`componentBaseChangeIso ≪≫ φ i ≪≫ (factorIso R B H i).symm`.

## Provenance

This module is an internal construction: bookkeeping for finite products of rings and disjoint
unions of spectra. It makes no claim beyond the stated isomorphisms and properties. It plays the
role of the step "replace a finite étale covering family by the single cover `∐ Spec R i`",
which Conrad uses implicitly when he writes "by étale descent we may work étale-locally"
(*Reductive group schemes*, 2014, proof of Proposition 6.4.4).
