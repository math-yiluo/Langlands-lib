# Proof of the actual-action simplicity and scalar-linearity reductions

`NonUnitalSimplicityProof.lean` proves the published derived target

```lean
Langlands.Algebra.CompatibleUnitization.NonUnitalSimplicityReductionStatement.{uK, uA, uM, uN}
```

from `Langlands.Algebra.NonUnitalSimplicityStatements`. The proof is the theorem
`Langlands.Algebra.CompatibleUnitization.nonUnitalSimplicityReduction`. Its type is exactly
that proposition, with the four independent universe parameters `uK`, `uA`, `uM`, `uN`. No
outer hypotheses are added. The statement pair and everything it imports are used unchanged.

The target is an internal comparison derived from Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026 (source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`). Its motivation is
the initial conventions (printed pp. 5–6 / PDF pp. 11–12), I.2.1 (printed p. 14 / PDF p. 20),
A.VI.3 (printed p. 263 / PDF p. 269) and B.II–III (printed pp. 272–273 / PDF pp. 278–279).
The statement's Markdown records these passages and the source distinctions. Renard does
not print this list of comparisons. The Lean proof below follows the annihilator/orbit route
described in the task context.

## The actual actions

Throughout, `ρ : A →ₙₐ[k] Module.End k M` is the given nonunital algebra homomorphism.
Every original-action notion uses the published local instance
`NonUnitalModule.ofLinearEndHom ρ`, whose scalar action is `a • m = ρ a m`. Every
unitized notion uses the published local instance `CompatibleUnitization.module ρ`, with
`x • m = x.fst • m + ρ x.snd m` (published lemma `smul_eq`). It restricts on `A` to `ρ`
(published lemma `inr_smul`). Both instances are introduced only locally: with `letI` in
definitions and term-mode proofs, and with `let` in tactic proofs. The statement elaborates them in the same way, and
no global instance is installed. **Additive simplicity** abbreviates, as in the statement's
Markdown, the exact proposition

```lean
Nontrivial M ∧ ∀ S : NonUnitalSubmodule A M, S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤
```

for the original action. It quantifies over all original stable additive subgroups, which
need not be closed under scalars.

## Auxiliary declarations

In `Langlands.Algebra.NonUnitalModuleCat`, for an object `X` of the published additive
category `NonUnitalModuleCat A`:

- `botSubmodule X` and `topSubmodule X` are the stable additive subgroups with underlying
  additive subgroups `⊥` and `⊤`.
- `toAddSubgroup_injective X` states that a `NonUnitalSubmodule` is determined by its
  underlying additive subgroup.
- `subobjectOrderIso_top X` states that the published correspondence
  `subobjectOrderIso X` sends the top subobject to `topSubmodule X`. The proof uses
  `Subobject.top_eq_id` and the published membership lemma `mem_subobjectOrderIso_mk`.
- `subobjectOrderIso_bot X` states that the correspondence sends the bottom subobject to
  `botSubmodule X`. It assumes `HasZeroObject` so that `⊥` exists in `Subobject X`. One
  inclusion holds because an order isomorphism sends `⊥` to a least element. The other holds
  because every stable additive subgroup contains `0`.
- `additiveSimple_iff_simple X` proves that additive simplicity of `X` is equivalent to
  `CategoryTheory.Simple X`.

In `Langlands.Algebra.CompatibleUnitization`, with the field-general variables of the
statement:

- `unitizedNonUnitalSubmodule ρ p` is a unitized submodule `p`, viewed as an original
  stable additive subgroup with the same carrier. Stability under `a` is stability under
  `Unitization.inr a`, rewritten by `inr_smul`.
- `annihilatorSubmodule ρ` is the common annihilator `{m | ∀ a, ρ a m = 0}`, a submodule for
  `module ρ`. It is closed under `x • m = x.fst • m + ρ x.snd m` because
  `ρ a (ρ b m) = ρ (a * b) m = 0`. The membership lemma `mem_annihilatorSubmodule` holds by
  definition.
- `orbitSubmodule ρ m` is the actual orbit `Set.range (fun a : A => ρ a m)`, a submodule
  for `module ρ`. It contains `ρ (a + b) m` and `ρ 0 m`. For the unitized action,
  `x • ρ a m = ρ (x.fst • a + x.snd * a) m`, by `k`-linearity and multiplicativity of `ρ`.
  The membership lemma `mem_orbitSubmodule` holds by definition.
- `annihilatorSubmodule_eq_bot` proves that, under unitized simplicity and `ρ ≠ 0`, the
  annihilator is `⊥`. If it were `⊤`, every `ρ a` would vanish on all of `M`, so `ρ = 0`.
- `orbit_surjective` proves that, under unitized simplicity and `ρ ≠ 0`, the map
  `fun a : A => ρ a m` is surjective for every `m ≠ 0`. Since the annihilator is zero, some
  `ρ a m` is nonzero. Thus `orbitSubmodule ρ m` is not `⊥`, so it is `⊤`.

## The seven comparisons

1. `compatibleSimpleUnitization ρ` proves `CompatibleSimpleUnitizationStatement ρ`. It
   transports `IsSimpleOrder` across the published order isomorphism `submoduleOrderIso ρ`
   between `CompatibleSubmodule ρ` and the unitized submodules (`OrderIso.isSimpleOrder_iff`).
   It then identifies the result with `IsSimpleModule` by `isSimpleModule_iff`.
2. `additiveSimpleCategorical ρ` proves `AdditiveSimpleCategoricalStatement ρ`. It applies
   `additiveSimple_iff_simple` to `NonUnitalModuleCat.of A M` for the original action. That
   proof first constructs, inside the proof only, the instances `HasFiniteBiproducts` (from the
   published `Preadditive` and `HasFiniteProducts` instances, via
   `HasFiniteBiproducts.of_hasFiniteProducts`) and then `HasZeroObject`
   (`hasZeroObject_of_hasFiniteBiproducts`). No global zero-object instance is added. Mathlib's
   `simple_iff_subobject_isSimpleOrder` then reduces `Simple X` to
   `IsSimpleOrder (Subobject X)`. The published `subobjectOrderIso X` carries `⊥` and `⊤` to
   `botSubmodule X` and `topSubmodule X`. These are the stable additive subgroups with underlying
   subgroups `⊥` and `⊤`, and `toAddSubgroup_injective` compares them. Distinctness of `⊥`
   and `⊤` in `Subobject X` corresponds to `Nontrivial X`: if `X` were a subsingleton, the
   two image subgroups would coincide. This comparison uses only the variables of its
   statement and no multiplication-bilinearity instances.
3. `additiveSimpleUnitization ρ` proves `AdditiveSimpleUnitizationStatement ρ`. Nontriviality
   of the unitized submodule lattice comes from `Nontrivial M` (`Submodule.nontrivial_iff`).
   Each unitized submodule `p` gives `unitizedNonUnitalSubmodule ρ p`, whose underlying
   additive subgroup is `⊥` or `⊤` by additive simplicity. Thus `p = ⊥` or `p = ⊤`.
4. `simpleUnitizationRestriction ρ` proves `SimpleUnitizationRestrictionStatement ρ`.
   `Nontrivial M` comes from `IsSimpleModule.nontrivial`. A stable additive subgroup `S` that
   is not `⊥` contains some `m ≠ 0`. By `orbit_surjective`, every `n` equals `ρ a m` for
   some `a`. Then `n ∈ S` by original stability `S.smul_mem'`, so `S` is `⊤`.
5. `simpleUnitizationOrbit ρ` proves `SimpleUnitizationOrbitStatement ρ`; it is
   `orbit_surjective`.
6. `simpleUnitizationIntertwiner ρ` proves `SimpleUnitizationIntertwinerStatement ρ` for any
   target `N : Type uN` with any compatible action `σ`. Fix `m₀ ≠ 0` in the nontrivial source.
   By `orbit_surjective`, write `m = ρ a m₀`. The original intertwining equation
   `f (ρ b m₀) = σ b (f m₀)` is `f.map_smul'` for the two actual original actions. Since
   `c • ρ a m₀ = ρ (c • a) m₀`, we get
   `f (c • m) = σ (c • a) (f m₀) = c • σ a (f m₀) = c • f m`. Only the compatible action
   `σ` on the target is used; no simplicity or nonzero action is assumed there.
7. `complexAdditiveSimpleActionNonzero` proves `ComplexAdditiveSimpleActionNonzeroStatement`.
   Suppose `ρ = 0` and fix `m ≠ 0`. The cyclic subgroup `AddSubgroup.zmultiples m` is
   stable, since every `ρ a` is zero. It is not `⊥` because it contains `m`. If it were `⊤`,
   then `(1/2) • m = n • m` for some integer `n`. Rewriting `n • m` as `(n : ℂ) • m`
   (`Int.cast_smul_eq_zsmul`) gives `((n : ℂ) - 1/2) • m = 0`. Since `m ≠ 0`,
   `(n : ℂ) = 1/2`, so `2 * n = 1` in `ℤ` (by `linear_combination` and `Int.cast_injective`).
   `omega` rules this out.

The aggregate `nonUnitalSimplicityReduction` packages comparisons 1–6 for every field-general
`ρ`, and comparison 7, into exactly `NonUnitalSimplicityReductionStatement.{uK, uA, uM, uN}`.

## The zero-action boundary

The theorem `zeroComplexAction_simple_not_additiveSimple` checks the counterexample from the
statement's Markdown. For `A = ℂ`, `M = ℂ` and `ρ = 0`, it proves both of the following:

- the unitized module is simple. With `CompatibleUnitization.isScalarTower`, each unitized
  submodule restricts to a `ℂ`-submodule of `ℂ`. That submodule is `⊥` or `⊤`, because `ℂ`
  is a simple module over itself. The equivalences `Submodule.restrictScalars_eq_bot_iff` and
  `Submodule.restrictScalars_eq_top_iff` then transfer this back.
- the original action is not additively simple, by comparison 7.

Thus the premise `ρ ≠ 0` cannot be dropped from comparison 4. This extra theorem is not part
of the target; the zero-action and zero-carrier cases of the target are covered by the
aggregate itself.

## Checking

The module compiles in the pinned environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with
no errors and no warnings. Inspection of `nonUnitalSimplicityReduction` reports a theorem
with universe parameters `uK, uA, uM, uN`. Its axioms are only `propext`,
`Classical.choice` and `Quot.sound`. No `sorry`, `admit` or new axiom is used.

## Attribution

Worker 751 wrote the Lean proof and this documentation. Worker 6 supplied the route that the
proof implements: the annihilator/orbit argument, automatic scalar linearity and the complex
cyclic-subgroup obstruction. Worker 6 is credited as a coauthor. Worker 709 formulated and
audited the target statement pair, which is used unchanged.
