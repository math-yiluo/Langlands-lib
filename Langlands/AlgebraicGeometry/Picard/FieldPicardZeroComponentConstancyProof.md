# Constancy of the geometric Picard-zero condition on connected components: proof

Author: Worker 1028.

This module proves the exact published proposition
`Langlands.AbelianScheme.FieldPicardZeroComponentConstancyStatement.{u}`
(theorem `Langlands.AbelianScheme.fieldPicardZeroComponentConstancy`). It
uses three published propositions through their published proofs:

- `Langlands.AbelianScheme.UniversalMumfordClassifierStatement`
  (proof module `Langlands.AlgebraicGeometry.Picard.UniversalMumfordClassifierProof`);
- `Langlands.AbelianScheme.FibreContractionOpenStatement`
  (proof module `Langlands.AlgebraicGeometry.Picard.FibreContractionOpenProof`);
- `Langlands.GroupScheme.FieldGroupOpenSubgroupClosedStatement`
  (proof module `Langlands.AlgebraicGeometry.Picard.FieldGroupOpenSubgroupClosedProof`).

Each is applied through the theorem that proves the exact proposition, so the
proof depends only on the published statements, not on internal lemmas of the
proof modules.

The proof follows the idea behind Lemma (7.15) of Edixhoven, van der Geer and
Moonen, *Abelian Varieties* (preliminary draft, source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, printed p.104, PDF
p.108): the vanishing locus of `ϕ` on the universal parameter is open and
closed. It uses neither a Hom-scheme nor étaleness: openness comes from a
rigidity argument and closedness from the group law of the parameter.

## Setting

Fix a field `k : Type u`, `S = Spec k`, `A : AbelianScheme S`, `P : Over S`,
`L : RigidifiedFamily A P` with `LocallyOfFiniteType P.hom` and full
universality `hL`. Let `B = (baseChange P.hom).obj A`, the abelian scheme
`A ×_S P` over `P.left`.

1. `universalMumfordClassifier` (a proof of
   `UniversalMumfordClassifierStatement`) gives `Ψ : B.X.left ⟶ P.left` over `S`
   with `unitSection B ≫ Ψ = P.hom ≫ e`, where `e` is the underlying morphism
   of the published `trivialParameter`, and with the Picard-zero criterion
   for every pullback of `L` (see `UniversalMumfordClassifierStatement.md`).
2. `e` is a section of `P.hom`, so it is a closed immersion
   (`isClosedImmersion_of_comp_eq_id`, as `Spec k` has one point). Its image
   is the single closed point `e₀`.
3. Put `U = {y : P.left | ∀ z, B.X.hom z = y → Ψ z = e₀}`, the set of points
   over whose fibre `Ψ` is constantly the trivial parameter.

## Steps

- **Openness.** `fibreContractionOpen` (a proof of
  `FibreContractionOpenStatement`), applied to `B`, `Ψ` and `e₀`, shows that
  `U` is open, because `Ψ` sends the unit section to `e₀`.
- **Rational points** (`ComponentConstancy.eq_comp_of_range_subset_range`).
  If `e` is a section of `f : X ⟶ S'` with `S'` a one-point scheme and
  `g : T ⟶ X` has reduced source and image inside the image of `e`, then
  `g = (g ≫ f) ≫ e`. Proof: `e` is a closed immersion; the base change of `e`
  along `g` is a surjective closed immersion onto the reduced scheme `T`,
  hence an isomorphism (`isIso_of_isClosedImmersion_of_surjective`), so `g`
  factors through `e`.
- **Geometric points and `U`** (`key` in the proof). For an algebraically
  closed `K`, `b : Spec K ⟶ S` and `p : Over.mk b ⟶ P`, the actual pullback of
  `L` along `p` is `IsPicardZeroFamily` exactly when the image of `p.left`
  lies in `U`.
  - Forward: the criterion of step 1 with `t = 𝟙` says that `Ψ` maps every
    `K`-point of the fibre `F = B ×_{P} Spec K` to `e₀`. `F` is locally of
    finite type over `Spec K`, hence a Jacobson space whose closed points are
    `K`-points (`pointOfClosedPoint`). The closed set `(F ⟶ B ⟶ P)⁻¹{e₀}`
    contains all closed points, so it is everything (`closure_closedPoints`).
    Every point of `B` over the image point lifts to `F`
    (`Scheme.Pullback.exists_preimage_pullback`).
  - Backward: every geometric point `y` of `B` over `t ≫ p.left` has image in
    the fibre over a point of `U`, so `y ≫ Ψ` has image `{e₀}`; the
    rational-point lemma and `Ψ ≫ P.hom = B.X.hom ≫ P.hom` give
    `y ≫ Ψ = t ≫ b ≫ e`, which is the criterion of step 1.
- **Group property.** The published `universalCommGrpObj` (built from the
  proved coherence theorems `pullbackTensorComparisonIsIso`,
  `pullbackTensorUnitCoherence`, `explicitPullbackTensorAssociativity`,
  `tensorMonoidalLeftUnitorComparison`, `pullbackTensorSymmetry`,
  `locallyFreeRankOneIffTensorInvertible`, `pullbackTensorComposition`) makes
  `P` a commutative group object. `ComponentConstancy.isPicardZeroFamily_mul_inv`
  shows that for `p q : T ⟶ P` with Picard-zero pullbacks, the pullback along
  `p * q⁻¹` is Picard zero: `classifyingMap_mul` and `classifyingMap_inv`
  identify its class with `[p^*L] · [q^*L]⁻¹`, and
  `ComponentConstancy.isPicardZeroClass_mul_inv` shows that the
  Picard-zero classes are closed under `a, b ↦ a b⁻¹` in the group
  `classesCommGroup`, using the published subgroup structure
  `picardZeroClassesCommGroup` and uniqueness of inverses.
- **Closedness.** By the previous two items, the `K`-points of `P` with image
  in `U` are closed under `p, q ↦ p * q⁻¹` for every algebraically closed
  `K`. Since `P.hom` is locally of finite type,
  `GroupScheme.fieldGroupOpenSubgroupClosed` (a proof of
  `FieldGroupOpenSubgroupClosedStatement`), applied to `k`, `P` with the group
  object `universalCommGrpObj` and `U`, shows that `U` is closed.
- **Conclusion.** The hypothesis on `s₀` and the key equivalence put the
  image of `s₀` in `U`. Since `U` is clopen, it contains the connected
  component of that point (`IsClopen.connectedComponent_subset`), which equals
  `connectedComponent x` (`connectedComponent_eq`). So the image of `s₁` lies
  in `U`, and the key equivalence for `Over.homMk s₁ rfl` gives the
  conclusion.

## Scope and dependencies

The field `k` is arbitrary, the fields `K₀` and `K₁` are arbitrary
algebraically closed fields in `Type u`, and the predicate compared is the
unchanged `IsPicardZeroFamily` on the actual pullbacks along
`Over.homMk s rfl`. No hypothesis beyond those of the statement is added:
the group law, the classifier, the rigidity openness and the closedness
argument are all proved here or in the published Library. The proof does not
use `FieldPicardZeroGeometricComponentComparisonStatement`,
`FieldPicardZeroGeometricOpenLocusStatement`,
`FieldPicardZeroOpenLocusStatement`, any supplied-open-locus result or
`IsPicardZeroOpenLocus`, and it does not import
`FieldPicardIdentityComponent`. Local finite type of `P.hom` is used only in
the closedness step (Jacobson property of the base change of `P` to an
algebraic closure).
