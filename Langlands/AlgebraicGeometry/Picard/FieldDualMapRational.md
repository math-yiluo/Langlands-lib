# Conditional rational dualization over a field

`Langlands.AbelianScheme.fieldDualHom0` extends the actual additive
Poincare-pullback dualization to the existing rational Hom groups:

`Hom0 A B →ₗ[ℚ] Hom0 FB FA`.

Here `FA` and `FB` are the constructed conditional dual abelian schemes
from `fieldDualAbelianSchemeFromEvaluation`, over the same arbitrary
field `k : Type u`. The direction is contravariant.

## Inputs and construction

The construction retains explicit proofs of
`FieldDualSchemeMapAdditivityStatement` and
`FieldDualSchemeGeometryStatement`. It also retains both actual
universal-family existence witnesses, both ordinary inverse bundles
on the parameter-first relative spaces, and both module-sheaf tensor
evaluation isomorphisms. The seven fixed-map hypotheses are
`pullbackTensorComparisonIsIsoStatement`,
`PullbackTensorCompositionStatement`,
`PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement`,
`PullbackTensorSymmetryStatement`, and `PicardZeroPullbackStatement`.
No chosen rational map or extra additivity assumption is added.

The existing `Hom0 A B` is `ℚ ⊗[ℤ] (A ⟶ B)`. First the constructed
`fieldDualAbelianSchemeMapAddHom` is viewed as a `ℤ`-linear map via
`toIntLinearMap`. Applying `LinearMap.baseChange ℚ` gives the displayed
`ℚ`-linear map. Thus its linearity laws come from scalar extension of
the actual additive map.

## Formulas and implemented proofs

`fieldDualHom0_tmul` states
`dual0(q ⊗ f) = q ⊗ dual(f)`, where `dual(f)` is exactly
`fieldDualAbelianSchemeMapFromEvaluation f`. It uses the scalar-extension
pure-tensor formula. `fieldDualHom0_homToHom0` specializes this to `q = 1`,
so it commutes with the published integral-to-rational maps.

`fieldDualHom0_unique` proves uniqueness among `ℚ`-linear maps with that
integral formula. Tensor induction reduces the claim to pure tensors
and addition. A pure tensor `q ⊗ f` equals `q • homToHom0 f`, so
linearity and the integral formula settle that case; additivity settles
the sum case.

`fieldDualHom0_id` uses identical representability and inverse/evaluation
data at the two occurrences of `A`. It rewrites the rational identity as
`1 ⊗ id`, applies the pure-tensor formula, and uses the published identity
law for the integral dual map.

`fieldDualHom0_comp` takes a third abelian scheme and its own
representability and inverse/evaluation data. For `f : Hom0 A B` and
`g : Hom0 B C`, it proves

`dual0(comp0 A B C f g) = comp0 FC FB FA (dual0 g) (dual0 f)`.

Double tensor induction reduces this to integral morphisms. The
published pure-tensor composition formula, the integral reversed
composition law, and commutativity of rational multiplication prove
the pure case. The remaining cases use linearity in both variables.

## Provenance and limitations

This is a derived algebraic construction from the existing `Hom0`,
actual additive dual map, and integral identity/composition laws.
Edixhoven-van der Geer-Moonen, *Abelian Varieties*, preliminary draft,
Chapter VII, Lemma (7.16)(i) and Corollary (7.17), printed p.104
(PDF p.108), supplies the geometric motivation for the explicit
additivity hypothesis. Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
No source errata note was present in the admission Library. The scalar
extension and uniqueness proof here are algebraic deductions, not a
claim that this passage states the Lean rational construction.

No proof of the geometric additivity or geometry statements is supplied.
Their separate proof tasks are respectively
`b71714f0-c50a-4258-94ac-e065ce455f61` and
`19d345c7-a011-41ac-a9b9-bb37a32f14a1`. Universal-family existence and
ordinary inverse/evaluation data remain conditional, as do the seven
fixed-map propositions. This module is field-only and does not supply
arbitrary-base dual geometry, biduality, polarizations, or Rosati.
