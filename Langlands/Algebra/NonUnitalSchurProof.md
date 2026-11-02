# Proof of Renard B.II for the original nonunital action

`NonUnitalSchurProof.lean` proves the published target

```lean
Langlands.Renard.NonUnitalSchurStatement.{uA, uM}
```

from `Langlands.Algebra.NonUnitalSchurStatements`. The proof is the theorem
`Langlands.Renard.nonUnitalSchur`. Its type is exactly that proposition, with the two
independent universe parameters `uA` (algebra) and `uM` (carrier). No outer hypotheses are
added. The statement pair and everything it imports are used unchanged.

## Source

The theorem is B.II of David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026 (source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`), printed p. 272 /
PDF p. 278. The initial conventions (printed pp. 5–6 / PDF pp. 11–12) allow nonunital
rings and actions. I.2.1 (printed p. 14 / PDF p. 20) distinguishes additive intertwiners
from complex-linear ones. The statement's Markdown explains how these conventions give
the targets: every stable additive subgroup is tested, and every additive original-action
endomorphism is kept.

Renard's proof adjoins a unit to the algebra. It shows that a nonzero endomorphism has
kernel `0` and image `M`, and that the orbit `A · m` is `M` for `m ≠ 0`. It then shows that
evaluation `f ↦ f(m)` is injective, which bounds dimensions, and applies B.I (Amitsur). The
Lean proof follows the same outline. It runs the unitization step through the published
nonunital simplicity reductions, and the kernel/image, evaluation and Amitsur steps through
the published unital Schur proofs. Components 3 and 4 and the rank bounds are proved
directly on the original action, as described below.

## The actual actions

Throughout, `ρ : A →ₙₐ[ℂ] Module.End ℂ M` is the given action. The algebra has
`[NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]`, and the
carrier has `[AddCommGroup M] [Module ℂ M]`.

- Every original-action notion uses the published local instance
  `NonUnitalModule.ofLinearEndHom ρ`, with `a • m = ρ a m`. This includes
  `NonUnitalSubmodule A M`, `NonUnitalModuleHom A M M` and
  `CategoryTheory.End (NonUnitalModuleCat.of A M)`.
- Every unitized notion uses the published local instance `CompatibleUnitization.module ρ`
  of `Module (Unitization ℂ A) M`, with `x • m = x.fst • m + ρ x.snd m`.
- Where the unital Schur theorems need `IsScalarTower ℂ (Unitization ℂ A) M`, and wherever
  `CompatibleUnitization.endAlgEquiv ρ` is used, the published local instances
  `CompatibleUnitization.isScalarTower ρ` and `CompatibleUnitization.smulCommClass' ρ`
  are added. The algebra `Algebra ℂ (Unitization ℂ A)` is Mathlib's.

All of these instances are introduced locally: with `letI` in definitions, statements and
term-mode proofs, and with `let` in tactic proofs. No global instance is installed.
**Additive simplicity** abbreviates the exact premise shared by all nine components:

```lean
letI := NonUnitalModule.ofLinearEndHom ρ;
Nontrivial M ∧ ∀ S : NonUnitalSubmodule A M, S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤
```

No component assumes `ρ ≠ 0`, a unit, finite dimension or a cyclic vector. The nonzero
action is derived below.

## Reused published results

From the nonunital simplicity proof (task `945162d2-93c9-43f8-9041-45179cf2c0f5`), all in
`Langlands.Algebra.CompatibleUnitization`:

- `complexAdditiveSimpleActionNonzero`: additive simplicity implies `ρ ≠ 0` in the complex
  setting;
- `additiveSimpleUnitization ρ`: additive simplicity implies that `module ρ` is a simple
  `Unitization ℂ A`-module;
- `simpleUnitizationOrbit ρ`: given `ρ ≠ 0` and unitized simplicity,
  `fun a : A => ρ a m` is surjective for every `m ≠ 0`;
- `simpleUnitizationIntertwiner ρ`: given `ρ ≠ 0` and unitized simplicity, every additive
  original intertwiner from `M` to another compatible module is complex-linear.

From the unital Schur proof (task `002527a3-e4ad-41b7-80b0-90372fcaa508`), all in
`Langlands.Renard` and all applied to `A := Unitization ℂ A` with `module ρ`:
`schurEndDivision`, `schurEndBijective`, `schurEvaluationInjective` and
`schurScalarOfModuleRankCountable`.

From `Langlands.Algebra.CompatibleUnitization`: `centralizer ρ`, `mem_centralizer_iff`
(membership means `f (ρ a m) = ρ a (f m)`) and the algebra equivalence
`endAlgEquiv ρ : centralizer ρ ≃ₐ[ℂ] Module.End (Unitization ℂ A) M`. The equivalence does
not change the underlying function, and it commutes with the scalar algebra maps.

None of these proof engines is reproved here.

## Auxiliary declarations

All helpers are in the namespace `Langlands.Renard.NonUnitalSchur`.

- `orbitMap ρ m : A →ₗ[ℂ] M` is `a ↦ ρ a m`. It is complex-linear because `ρ` is additive
  and `ℂ`-equivariant (`map_add`, `map_smul`). It is a linear map out of the original `A`,
  not out of the unitization.
- `evaluationMap ρ m : centralizer ρ →ₗ[ℂ] M` is `g ↦ g m`. Linearity holds by definition.
- `ofCentralizer ρ g : NonUnitalModuleHom A M M` is the additive original endomorphism with
  the same underlying function as `g : centralizer ρ`. Its intertwining identity is
  `mem_centralizer_iff`.

The remaining helpers assume additive simplicity `hs`.

- `action_ne_zero ρ hs : ρ ≠ 0` is `complexAdditiveSimpleActionNonzero ρ hs`.
- `unitized_isSimpleModule ρ hs` is `additiveSimpleUnitization ρ hs`.
- `map_complex_smul ρ hs` states that every `f : NonUnitalModuleHom A M M` satisfies
  `f (c • m) = c • f m`. It is `simpleUnitizationIntertwiner` with target `N := M` and
  target action `σ := ρ`.
- `linearMapOf ρ hs f : Module.End ℂ M` has the same function as `f`. Additivity is
  `f.map_add`, and scalar linearity is `map_complex_smul`.
- `linearMapOf_mem_centralizer` places it in `centralizer ρ`. The original intertwining
  identity `f.map_smul' a m : f (ρ a m) = ρ a (f m)` is exactly the membership condition.
- `toCentralizer ρ hs f : centralizer ρ` packages the two. `toCentralizer_apply` holds by
  definition.
- `endRingEquiv ρ hs` is a ring equivalence between
  `CategoryTheory.End (NonUnitalModuleCat.of A M)` and `centralizer ρ`. Its forward map is
  `toCentralizer` and its inverse is `ofCentralizer`. Both round trips, multiplication and
  addition hold by `rfl`. In the published category, composition is function composition and
  addition is pointwise, and the same holds in `Module.End ℂ M`. The source carries the
  ring structure found by instance search, as in the statement. That is Mathlib's ring on
  `End X` for the published `Preadditive` instance `NonUnitalModuleCat.preadditive`.
- `unitizedEndRingEquiv ρ hs` composes `endRingEquiv ρ hs` with
  `(endAlgEquiv ρ).toRingEquiv`, giving
  `CategoryTheory.End (NonUnitalModuleCat.of A M) ≃+* Module.End (Unitization ℂ A) M`.
  `unitizedEndRingEquiv_apply` records, by `rfl`, that it preserves underlying functions.

## The nine components

All component theorems are in `Langlands.Renard` and take the full statement telescope
`{A} [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] {M}
[AddCommGroup M] [Module ℂ M] (ρ)`.

1. `nonUnitalSchurEndDivision ρ : NonUnitalSchurEndDivisionStatement ρ`. Write
   `e := unitizedEndRingEquiv ρ hs`. `schurEndDivision` on the simple unitized module gives
   a nontrivial `Module.End (Unitization ℂ A) M` in which every nonzero element is a unit.
   Nontriviality pulls back along the surjective `e` (`Function.Surjective.nontrivial`).
   For `f ≠ 0`, `e f ≠ 0` because `e` is injective (`map_ne_zero_iff`). So `e f` is a
   unit, and `f` is a unit by `MulEquiv.isUnit_map`.
2. `nonUnitalSchurEndBijective ρ : NonUnitalSchurEndBijectiveStatement ρ`. For `f ≠ 0`,
   `e f ≠ 0`, and `schurEndBijective` makes `e f` bijective. Since `e f` has the same
   underlying function as `f`, `f` is bijective. This is the source's kernel/image step,
   imported from the unital proof.
3. `nonUnitalSchurEndComparison ρ : NonUnitalSchurEndComparisonStatement ρ`. Existence is
   `toCentralizer ρ hs f`, which agrees with `f` by definition. For uniqueness, any
   `g : centralizer ρ` that agrees with `f` pointwise equals it by `Subtype.ext` and
   `LinearMap.ext`. No scalar structure is put on the whole type `NonUnitalModuleHom A M M`.
4. `nonUnitalSchurCyclicMapSurjective ρ : NonUnitalSchurCyclicMapSurjectiveStatement ρ` is
   `simpleUnitizationOrbit ρ (action_ne_zero ρ hs) (unitized_isSimpleModule ρ hs)`. This
   is surjectivity of the original orbit map `fun a : A => ρ a m`.
5. `nonUnitalSchurEvaluationInjective ρ : NonUnitalSchurEvaluationInjectiveStatement ρ`.
   Let `g₁ m = g₂ m`. This equation is, by definition,
   `endAlgEquiv ρ g₁ m = endAlgEquiv ρ g₂ m`. `schurEvaluationInjective` on the unitized
   module gives `endAlgEquiv ρ g₁ = endAlgEquiv ρ g₂`, and injectivity of `endAlgEquiv ρ`
   gives `g₁ = g₂`.
6. `nonUnitalSchurModuleRankCountable ρ : NonUnitalSchurModuleRankCountableStatement ρ`.
   Choose `m ≠ 0` from `Nontrivial M`. By component 4, `orbitMap ρ m` is surjective, so
   `LinearMap.lift_rank_le_of_surjective` gives
   `Cardinal.lift.{uA} (Module.rank ℂ M) ≤ Cardinal.lift.{uM} (Module.rank ℂ A)`.
   `Cardinal.lift_le_aleph0` moves `Module.rank ℂ A ≤ ℵ₀` and the conclusion
   `Module.rank ℂ M ≤ ℵ₀` across the lifts. The universes `uA` and `uM` are never equated.
7. `nonUnitalSchurEndRankCountable ρ : NonUnitalSchurEndRankCountableStatement ρ`. Choose
   `m ≠ 0`. By component 5, `evaluationMap ρ m` is injective, so
   `LinearMap.rank_le_of_injective` gives
   `Module.rank ℂ (centralizer ρ) ≤ Module.rank ℂ M ≤ ℵ₀`. Both types live in `Type uM`,
   so no lift is needed.
8. `nonUnitalSchurScalarOfModuleRankCountable ρ :
   NonUnitalSchurScalarOfModuleRankCountableStatement ρ` combines two helpers.
   - `NonUnitalSchur.algebraMap_bijective`: `schurScalarOfModuleRankCountable` on the
     unitized module makes `algebraMap ℂ (Module.End (Unitization ℂ A) M)` bijective.
     Since `endAlgEquiv ρ` commutes with scalars (`AlgEquiv.commutes`),
     `algebraMap ℂ (centralizer ρ)` equals `(endAlgEquiv ρ).symm ∘ algebraMap ℂ
     (Module.End (Unitization ℂ A) M)`. A composite of bijections is bijective.
   - `NonUnitalSchur.existsUnique_smul_of_bijective`: given bijectivity of
     `algebraMap ℂ (centralizer ρ)`, every `f : NonUnitalModuleHom A M M` is multiplication
     by a unique scalar. Surjectivity gives `z` with `algebraMap z = toCentralizer ρ hs f`.
     Evaluating at `m` gives `f m = z • m`, since `algebraMap z` acts as `m ↦ z • m`. If
     also `f m = w • m` for all `m`, then `algebraMap w = toCentralizer ρ hs f` by
     extensionality, so `w = z` by injectivity.
9. `nonUnitalSchurScalarOfAlgebraRankCountable ρ :
   NonUnitalSchurScalarOfAlgebraRankCountableStatement ρ` is component 6 followed by
   component 8.

The aggregate `nonUnitalSchur` packages the nine components for every `ρ`, in the
statement's order.

## Checking

The module compiles in the pinned environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with
no errors and no warnings (lake build). Inspection of `nonUnitalSchur` reports a theorem
with universe parameters `uA, uM`. Its axioms are only `propext`, `Classical.choice` and
`Quot.sound`. A separate check, kept out of the submission, assigned each of the nine
unapplied constants (`@nonUnitalSchurEndDivision.{uA, uM}`, …) to the complete explicit
telescope of its component statement. It also assigned `@nonUnitalSchur.{uA, uM}` to
`NonUnitalSchurStatement.{uA, uM}`, and `@nonUnitalSchur.{uA, uA}` to the equal-universe
instance. Every check compiled. No `sorry`, `admit` or new axiom is used.

## Attribution

Worker 751 wrote the Lean proof and this documentation. The route follows the
implementation suggestion in the task context and in the "Proof boundary and route" section
of the statement's Markdown, whose authors are Worker 709 and Worker 6. Worker 709
formulated and audited the target statement pair, which is used unchanged. Worker 6
contributed its source-convention clarification. The reused simplicity reductions were
written by Worker 751, with Worker 6 as coauthor. The reused unital Schur proofs were
written by Worker 972.
