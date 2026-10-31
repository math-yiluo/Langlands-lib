# Additive stable generation and actual finite localization

Author: Worker 490, for proof task
`551264ec-c65e-43eb-8047-daafd431ed28` revision 1.

The theorem `Langlands.Renard.additiveScalarFiniteLocalization` has exactly
the complete closed type
`Langlands.Renard.AdditiveScalarFiniteLocalizationStatement.{uR, uB, uV}`
from `Langlands.Algebra.RenardAdditiveScalarFiniteLocalizationStatements`.
Its three clauses, in the published order, are the generic module generation
comparison, the generic all-submodules generation comparison, and the actual
complex localization consequence. Each component also has a named proof.
The coefficient, algebra and carrier universes are independent, in that order;
the complex component retains independent algebra and carrier universes.

## Generic comparisons

Both proofs are in `Langlands.Algebra.AdditiveScalarStableGeneration`.
They use the given action `ρ : B →ₙₐ[R] Module.End R V` throughout.
The map `Submodule.toAddSubgroup` retains precisely the same underlying set.
Thus membership, containment of the finite generating set, and stability under
`ρ` pass to the underlying additive subgroup without modification.

For `moduleGenerationComparison`, take the finite set `S` supplied by the
additive generation hypothesis. If a stable scalar-linear submodule `P`
contains `S`, its actual underlying additive subgroup is stable and contains
`S`. The hypothesis makes that subgroup top.
`Submodule.toAddSubgroup_eq_top.mp` then gives `P = ⊤`. The proof returns
the same `S`, establishing `ModuleGenerationComparisonStatement`.

For `submoduleGenerationComparison`, apply the additive hypothesis to the
underlying additive subgroup of the given stable scalar-linear submodule
`P`. It supplies a finite set `S` contained in `P`, with the property that
every stable additive subgroup containing `S` contains `P`. Given a stable
scalar-linear submodule `Q` containing `S`, apply this property to
`Q.toAddSubgroup`. Its conclusion is the required `P ≤ Q`, since both
underlying sets are unchanged. This proves
`SubmoduleGenerationComparisonStatement`, again retaining the same generators.

The generic assumptions are exactly the published ones: a commutative
coefficient ring, a possibly nonunital and noncommutative algebra with its
written scalar compatibility instances, and a module with an additive
commutative group. Scalar closure of a submodule is only forgotten when
applying an additive hypothesis.

## Actual localization consequence

In namespace `Langlands.Renard.AlgebraActionLocalization`,
`additiveIdealFiniteLocalization` proves exactly
`AdditiveIdealFiniteLocalizationStatement.{uB, uV}`. After introducing the
original `B`, `V`, action `ρ`, self-intertwiner `f` and three additive
generation assumptions `hB`, `hV`, `hL`, the proof names

`σ = localizedAction f.toLinearMap ρ (fun b v => f.map_action' b v)`.

This is the actual localized action in the target. The proof converts the
three additive hypotheses to the three scalar-linear hypotheses of the
published `stableIdealFiniteLocalization`, imported from
`Langlands.Algebra.RenardStableIdealFiniteLocalizationProof`:

- Apply `submoduleGenerationComparison` to `R = ℂ`, the carrier `B` and
  the actual regular left action `NonUnitalAlgHom.lmul ℂ B`. Its evaluation
  on `b` and `x` is definitionally `b * x`, so `hB` supplies exactly the
  needed additive hypothesis. The conclusion gives finite stable generation
  of every complex-linear left ideal.
- Apply `moduleGenerationComparison` to the original carrier `V` and action
  `ρ`, using `hV`.
- Apply the same comparison to the actual carrier
  `Localized f.toLinearMap` and its action `σ`, using `hL`. The target's
  local definitions unfold to precisely these inputs.

The existing theorem then gives the unchanged conjunction
`CompatibleLocalizationStabilizationAt ρ f` and, for every positive `n`
with `Stable (f.toLinearMap ^ n)`, `CompatibleStablePowerImageAt ρ f n`.
These predicates retain surjectivity of the actual canonical map and one
positive common kernel/stability exponent, together with complementary
compatible kernel and image and the unique normalized compatible linear
equivalence to every positive stable power image. The equivalence preserves
the actions and operators; its inverse is the restriction of the actual
canonical map. No localization, action, intertwiner or conclusion is replaced.

Finally, `additiveScalarFiniteLocalization` assembles the three named proofs
in the required order. No premise is added to the closed theorem. The module
also checks its complete unapplied type at the unequal universe assignments
`(0, 1, 2)` and `(2, 1, 0)`.

## Provenance and scope

This proof is derived internal algebra. The governing source motivation and
original-source reading record belong to the unchanged statement pair:
David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, printed p. 6 / PDF p. 12 and printed p. 279 /
PDF p. 285, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The present argument proves that exact published internal target and makes
no new claim about the source's finiteness terminology or its proof route.
The imported scalar-linear finite-localization theorem supplies all the
localization conclusions; its own proof and provenance remain in its pair.

The result permits nonunital and noncommutative algebras, degenerate actions,
zero rings and modules, and arbitrary carrier dimension. It requires neither
a unit-action law nor nondegeneracy, nontriviality or finite dimension. It
asserts only the written additive-to-scalar sufficient conditions. Reverse
generation implications, identification of Renard's nonunital finiteness
convention, the source-facing C.II proposition, the other appendices and the
whole book retain their separate obligations. This proof adds no category
equivalence, unitization action or localization construction.
