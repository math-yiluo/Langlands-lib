# Renard A.VIII.2: proof that the regular unital module is a small progenerator

Author: Worker 734.

This proof unit targets the unchanged published proposition
`Langlands.Renard.RegularModuleSmallProgeneratorStatement`, imported from
`Langlands.CategoryTheory.Renard.RegularModuleSmallProgeneratorStatements`.
It works with the actual published predicates `HomSmallProgenerator`,
`HomProjective`, `HomPreservesCoproducts` and `HomGenerator`. These are
applied to the actual integer-module Hom functor `preadditiveCoyonedaInt` of
the actual lifted regular module `ModuleCat.of R (ULift.{v} R)`.

## Theorems and scope

All declarations belong to namespace `Langlands.Renard` in module
`Langlands.CategoryTheory.Renard.RegularModuleSmallProgenerator`. The common
context and the exported theorem signatures are:

```lean
universe w v u
variable (R : Type u) [Ring R]

theorem regularModule_homProjective :
  HomProjective (ModuleCat.of R (ULift.{v} R))

theorem regularModule_homPreservesCoproducts
    [HasCoproducts.{w} (ModuleCat.{max u v} R)] :
  HomPreservesCoproducts.{w} (ModuleCat.of R (ULift.{v} R))

theorem regularModule_homGenerator :
  HomGenerator (ModuleCat.of R (ULift.{v} R))

theorem regularModuleSmallProgenerator
    [HasCoproducts.{w} (ModuleCat.{max u v} R)] :
  RegularModuleSmallProgeneratorStatement.{w, v, u} R
```

The complete unapplied type of `regularModuleSmallProgenerator` is
`∀ (R : Type u) [Ring R] [HasCoproducts.{w} (ModuleCat.{max u v} R)],
RegularModuleSmallProgeneratorStatement.{w, v, u} R`, exactly the target's
telescope. The target unfolds definitionally to

```lean
(HomProjective P ∧ HomPreservesCoproducts.{w} P) ∧ HomGenerator P
```

with `P := ModuleCat.of R (ULift.{v} R)`, and the main theorem is the
anonymous constructor of the three component theorems in this arrangement.

The ring `R` is any unital ring. It may be noncommutative or the zero ring.
The universes `w`, `v` and `u` are independent and arbitrary. The only
hypothesis beyond `Ring R` is the bound `HasCoproducts.{w}` instance that
the target itself takes. The proof uses that instance only as the
argument the predicates require. It assumes or derives no relation between
`w` and `max u v`, specializes no universe, and adds no `Small`,
commutativity or nontriviality hypotheses. The target pair and all of its
imports are unchanged.

## Helper declarations

- `regularModuleSpanSingleton R x : ModuleCat.of R (ULift.{v} R) ⟶ X`, for
  `X : ModuleCat.{max u v} R` and `x : X`, is
  `ModuleCat.ofHom ((LinearMap.toSpanSingleton R X x).comp
  ULift.moduleEquiv.toLinearMap)`. It sends `ULift.up r` to `r • x`; this is
  the simp lemma `regularModuleSpanSingleton_apply`, proved by `rfl`.
- `regularModuleSpanSingleton_apply_one R f` states that every morphism
  `f` out of the lifted regular module equals
  `regularModuleSpanSingleton R (f.hom (ULift.up 1))`. The proof uses
  morphism extensionality on `ULift.up r`. The value
  `r • f.hom (ULift.up 1)` equals `f.hom (r • ULift.up 1)` by `map_smul`.
  The argument `r • ULift.up 1` is definitionally `ULift.up (r * 1)`, and
  `mul_one` finishes.

## Generator

`regularModule_isSeparator R` proves Mathlib's `IsSeparator` for the lifted
regular module directly. Mathlib's `ModuleCat.isSeparator` is stated for
`Shrink.{v} R` under `Small.{v} R`, so it is not used. Let `f g : X ⟶ Y` agree after
precomposition with every morphism from the regular module. The separator
hypothesis is applied to the singleton membership
`(ObjectProperty.singleton_iff _ _).mpr rfl` and to
`regularModuleSpanSingleton R x`. Evaluating both composites at
`ULift.up 1` gives `f (1 • x) = g (1 • x)`, and `one_smul` turns this into
`f x = g x`. Extensionality gives `f = g`.

`regularModule_homGenerator` then rewrites `HomGenerator` to `IsSeparator`
with the published `homGeneratorComparison` (module
`Langlands.CategoryTheory.Renard.HomGeneratorCriteria`), applied in the
abelian category `ModuleCat.{max u v} R`.

## Projectivity

`regularModule_homProjective` uses the published `homProjectiveComparison`
(module `Langlands.CategoryTheory.Renard.HomExactnessComparison`), which
identifies `HomProjective P` with Mathlib's `CategoryTheory.Projective P`.
The latter is found by instance inference. Mathlib's
`ModuleCat.projective_of_categoryTheory_projective` reduces it to
`Module.Projective R (ULift.{v} R)`. That instance is
`Module.instProjectiveULift` applied to `Module.Projective.of_free` for `R`
over itself.

## Coproduct preservation

The proof identifies the Hom functor with restriction of scalars along
`Int.castRingHom R : ℤ →+* R`. This functor is a left adjoint, so it
preserves colimits of every size.

- `regularModuleHomAddEquiv R X` is the additive equivalence from the
  carrier of `(preadditiveCoyonedaInt P).obj X`, which is `P ⟶ X`, to the
  carrier of `(ModuleCat.restrictScalars.{max u v} (Int.castRingHom R)).obj X`,
  which is `X`. The forward map is `f ↦ f.hom (ULift.up 1)`. The inverse is
  `x ↦ regularModuleSpanSingleton R x`, and
  `regularModuleSpanSingleton_apply_one` gives the left inverse. The right
  inverse is `one_smul`, and additivity holds by `rfl`.
- `regularModuleHomIso R X` upgrades this additive equivalence to an
  isomorphism in `ModuleCat.{max u v} ℤ`. It uses Mathlib's
  `AddEquiv.toIntLinearEquiv`, with the two integer-module structures given
  explicitly as the `isModule` fields of the two objects, and then
  `LinearEquiv.toModuleIso`. Since every additive map is linear for any two
  integer-module structures, this step does not compare the published
  integer action on the Hom module with the restricted action on `X`. The
  simp lemma `regularModuleHomIso_hom_apply` records that its forward
  component is `f ↦ f.hom (ULift.up 1)`; it is proved by `rfl`.
- `regularModuleHomFunctorIso R` is the natural isomorphism
  `preadditiveCoyonedaInt P ≅
  ModuleCat.restrictScalars.{max u v} (Int.castRingHom R)` built by
  `NatIso.ofComponents` from these components. Naturality holds
  elementwise by `rfl`: for `g : X ⟶ Y`, the Hom functor sends `f` to
  `f ≫ g`, whose value at `ULift.up 1` is `g` applied to `f (ULift.up 1)`.

`regularModule_homPreservesCoproducts` fixes `I : Type w`. Mathlib's
`ModuleCat.restrictCoextendScalarsAdj.{max u v} (Int.castRingHom R)`
exhibits restriction of scalars as left adjoint to coextension of scalars.
Its `leftAdjoint_preservesColimits` gives `PreservesColimitsOfSize.{w, w}`
for this `w`, with no existence or universe-relation assumption. Instance
inference specializes this to the shape `Discrete I`.
`preservesColimitsOfShape_of_natIso` transfers it along the inverse of
`regularModuleHomFunctorIso R`. The bound `HasCoproducts.{w}` instance is not used here
beyond being the argument the predicate requires.

## Sources and provenance

The asserted result is from David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, Appendix A.VIII.2,
printed page 267 / PDF page 273. The remark after the equivalence theorem
reads "On a bien sûr la réciproque, puisque un anneau unitaire A est un petit
progénérateur de M(A)". Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The
source gives no proof. The 2010 errata
(`renard-2010-corrections-complements`, PDF pages 18–19) contain nothing on
this remark. The proof route above is internal: evaluation at the unit and
restriction of scalars as a left adjoint. Its formulation with the published
comparisons and Mathlib's adjunction is not taken from the source.

The reused Mathlib declarations are from commit
`5ed2965256430c3649e86755f9576b54eca72435`:
`LinearMap.toSpanSingleton` (`LinearAlgebra/Span/Basic.lean`),
`ULift.moduleEquiv` (`Algebra/Module/ULift.lean`),
`AddEquiv.toIntLinearEquiv` (`Algebra/Module/Equiv/Basic.lean`),
`LinearEquiv.toModuleIso` (`Algebra/Category/ModuleCat/Basic.lean`),
`ModuleCat.restrictCoextendScalarsAdj`
(`Algebra/Category/ModuleCat/ChangeOfRings.lean`),
`Adjunction.leftAdjoint_preservesColimits`
(`CategoryTheory/Adjunction/Limits.lean`),
`preservesColimitsOfShape_of_natIso`
(`CategoryTheory/Limits/Preserves/Basic.lean`),
`ModuleCat.projective_of_categoryTheory_projective`
(`Algebra/Category/ModuleCat/Projective.lean`), and
`Module.instProjectiveULift` and `Module.Projective.of_free`
(`Algebra/Module/Projective.lean`). The published comparisons
`homProjectiveComparison` and `homGeneratorComparison` are imported
unchanged.

This unit does not address the equivalence with right `End(P)`-modules, the
converse for categories equivalent to module categories, nonunital module
categories, or the finite-support and finite-type assertions.

## Development checks

Approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled the
module without warnings or errors. Lake build and declaration inspection of
`Langlands.Renard.regularModuleSmallProgenerator` completed without warnings
or errors in diagnostic `91568007-bcb7-4af7-8de0-482cc742a967`, over
Library commit `d8292e5e2ee514f9410e96a37b722b57f1e9de93`. The
inspection reports a theorem with independent level parameters `w, v, u` and only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. The inspected
type has SHA256
`faaa6c2f8630ea8998ebfb1b63b369399ef970a67e0b641db8058bd5e9f94db5`.

A private diagnostic, `7c2ff5ff-d6c8-45c2-8d25-c456fb82542f`, ran further
checks. It assigned the unapplied theorem to the full target telescope above
and checked the displayed unfolding by `rfl`. It found the projectivity
instances named above. It applied the theorem to `ℤ` at universes
`.{7, 3, 0}` under a supplied `HasCoproducts.{7}` hypothesis, and to the
zero ring `PUnit` and the noncommutative ring `Module.End ℤ (ℤ × ℤ)` at
`.{0, 0, 0}`. It also checked by `rfl` that the natural isomorphism's
component sends `f` to `f.hom (ULift.up 1)`, and by `one_smul` that its
inverse sends `x` to a morphism with value `x` at `ULift.up 1`. These are
development checks; independent semantic review, official exact-target
validation and publication are separate requirements.
