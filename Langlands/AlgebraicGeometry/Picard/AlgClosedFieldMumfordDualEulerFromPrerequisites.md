# The dual-side Euler characteristic from its prerequisite statements

Authors: Worker 935 wrote this module. It assembles Worker 1164's Steps 1–4
(`Langlands.AlgebraicGeometry.Picard.MumfordDualDirectImages`), Worker 943's Steps 5 and 7
(`Langlands.AlgebraicGeometry.Picard.AlgClosedFieldMumfordDualEulerReduction`) and Worker
935's Step 6 (`Langlands.AlgebraicGeometry.Picard.FiniteFlatPointFibreSections`).

Module `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldMumfordDualEulerFromPrerequisites`,
namespace `Langlands.AbelianScheme`.

## Role and provenance

This is internal infrastructure for task `6b1ab3e8-b3b0-4567-9251-7566e7a6dba3`, which
proves the published `Langlands.AbelianScheme.AlgClosedFieldMumfordDualEulerStatement`. The
source correspondence of that target was reviewed with the statement. It is the proof of
Edixhoven, van der Geer and Moonen, *Abelian Varieties* (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), (9.11), formulas (8)–(10), printed
p.132 (PDF p.136). This module proves the target from four published statements whose proofs
are not yet in the Library. The anchor proposition `AlgClosedFieldMumfordDualEulerReductionStatement`
is internal: it is exactly this implication, and it is proved in the same module. Once the
four prerequisite proofs are published, the task's final proof applies
`algClosedFieldMumfordDualEulerReduction` to them.

## The anchor statement

```lean
def AlgClosedFieldMumfordDualEulerReductionStatement : Prop :=
  AlgClosedFieldPoincareDirectImageStatement.{u} →
    FlatHigherDirectImageBaseChangeStatement.{u} →
    LineBundleHigherProjectionFormulaStatement.{u} →
    FieldDualSchemeGeometryStatement.{u} →
    AlgClosedFieldMumfordDualEulerStatement.{u}
```

The four hypotheses are published Library propositions, used unchanged:

- `AlgClosedFieldPoincareDirectImageStatement`: over an algebraically closed field, the
  higher direct images of the Poincaré bundle along `A ×_K D ⟶ D` vanish outside degree
  `g`. In degree `g` the direct image is `(e_D)_* 𝒪_K`, where `e_D = (dualOrigin A hA).left`
  is the origin of the dual.
- `FlatHigherDirectImageBaseChangeStatement`: flat base change for higher direct images of
  quasi-coherent modules along quasi-compact separated morphisms.
- `LineBundleHigherProjectionFormulaStatement`: the projection formula
  `L ⊗ Rⁿ f_* M ≅ Rⁿ f_*(f^* L ⊗ M)` for a line bundle `L`.
- `FieldDualSchemeGeometryStatement`: over a field, the chosen dual is smooth, proper and
  geometrically connected.

The conclusion is the unchanged target `AlgClosedFieldMumfordDualEulerStatement`.

## Proof of `algClosedFieldMumfordDualEulerReduction`

Introduce the hypotheses and all binders of the target: `K`, `A`, `hA`, `L`, `B`,
`evaluationB`, `M`, `evaluation`, the Mumford map `f` with `hf`, the instances
`IsFinite f.left` and `Flat f.left`, `g` with `A.HasRelativeDimension g`, `hQ` and the point
`y` of the dual. Write `p = pullback.fst A.X.hom A.X.hom` for the parameter projection,
`Q = m^* N ⊗ snd^* M` for the coefficient, and `N` for the normalized line bundle
(`RigidifiedLineBundle.forget` applied to `LineBundle.normalize …`). Its underlying module is
the target's `(LineBundle.normalize …).obj.carrier`.

1. Steps 1–4: `mumfordDual_higherDirectImage` (from the first three hypotheses) gives
   `Rⁿ p_* Q = 0` for `n ≠ g` and an isomorphism `R^g p_* Q ≅ N ⊗ f^*(e_D)_* 𝒪_K`.
2. The origin is a section: `e_D ≫ (dualScheme A hA).hom = 𝟙`, by `Over.w (dualOrigin A hA)`.
   Also `f.left ≫ (dualScheme A hA).hom = A.X.hom` by `Over.w f`.
3. Step 6, support: `hasFiniteClosedSupport_tensor_pullback_pushforward` (from the
   flat base change hypothesis) shows that `N ⊗ f^*(e_D)_* 𝒪_K` has finite closed support.
   The isomorphism of step 1 transfers this to `R^g p_* Q` (`hasFiniteClosedSupport_iff_of_iso`).
4. Step 5: `eulerCharacteristic_comp_eq_of_concentrated p A.X.hom Q g` rewrites the Euler
   characteristic along `(mumfordProduct A).hom = p ≫ A.X.hom` as
   `(-1)^g · dim_K Γ_{A.X.hom}(R^g p_* Q)`. The remaining goal is
   `dim_K Γ_{A.X.hom}(R^g p_* Q) = f.left.finrank y`.
5. Step 6, dimension: the isomorphism of step 1 identifies the dimension with
   `dim_K Γ_{A.X.hom}(N ⊗ f^*(e_D)_* 𝒪_K)`. By
   `finrank_relativeGlobalSections_tensor_pullback_pushforward`, applied at the point
   `(dualScheme A hA).hom y` of `Spec K`, this is the degree of `f.left` at
   `e_D((dualScheme A hA).hom y)`.
6. Step 7: `finrank_eq_of_fieldDualSchemeGeometry` (from the geometry hypothesis) says that
   the degree of `f.left` is the same at every point of the connected dual. So the degree at
   that point of the origin equals the degree at `y`.

The theorem uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## Assumptions

The four prerequisite statements are hypotheses here and are not proved in this module.
Their proof tasks are `32297f48` (Poincaré direct images), `5b778a75` (flat base change),
`d0088789` (higher projection formula) and `19d345c7` (geometry of the dual over a field).
