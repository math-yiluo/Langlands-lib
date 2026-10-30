# Noetherian actual localization of additive nonunital actions

Authors: Worker 709 and Worker 735. Worker 709 prepared this statement
unit under the whole-book Renard program; Worker 735 rechecked it and
submitted it for task `bd5e27f7-5edf-44f4-80ea-521409c4c32b`. It imports
the published
`Langlands.Algebra.IntegerCompatibleNonUnitalAction` by Lean name and
reuses the existing actual localization and compatible unitization.
The file defines targets; it proves none of them.

## Provenance and limits

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Printed body page equals PDF page minus 6.

The final C.II proposition, printed 279 / PDF 285, motivates the
surjectivity and eventual-stability conclusions. Its source assumptions
are a commutative Noetherian complex algebra, a finite-type module and a
finite-type actual endomorphism localization. C.II, printed 276 / PDF 282,
defines stability by both kernel and image equalities and eventual
stability by a positive power. The actual localization comes from
A.III.1, example 5 and the following lemma/corollary, printed 252–253 /
PDF 258–259. Worker 709 has directly read these passages for the parent
localization branch. The conventions on printed 5–6 / PDF 11–12 and the
Hom distinction in I.2.1, printed 14 / PDF 20, with PDF 21 as context,
allow original additive nonunital actions without complex-linearity of
all morphisms. Worker 709 reread those conventions for the integer
compatibility dependency. Worker 735 independently read all of these
pages (PDF 285, 282, 258–259, 11–12 and 20–21) for this submission.

These targets are derived internal content. They use ordinary module
Noetherianity or finite generation over the actual integer unitization
`U = Unitization ℤ A`. They make no identification with Renard's
finite-type or Noetherian terminology, impose no complex vector-space
structure, and do not claim the complete final C.II proposition. The
source convention and the canonical action-compatible stable-image
identification remain separate obligations.

The registered supplementary `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is the older-edition corrections file in project literature. Workers 709
and 735 each read its Appendix C corrections on PDF 18–19, and Worker 735
rechecked its hash. These pages do not correct the final C.II proposition
or settle the nonunital finiteness conventions. They do not supersede the
2026 original. On 30 October 2026, Library commit `9330fa8d` had no
Renard errata note covering C.II. Its `notes/renard/appendix-a-corrections.md`
concerns A.III.1 example 4 and later Appendix A passages, not the example 5
localization used here.
This is a limited search, not a claim that no errata exist.

## Exact data and actions

The closed targets bind independent `uA` and `uV`, an arbitrary
`A : Type uA` with `NonUnitalRing A`, an arbitrary `V : Type uV` with
`AddCommGroup V`, its original `NonUnitalModule A V`, and an original
additive self-intertwiner `f : NonUnitalModuleHom A V V`. They impose no
unit law, commutativity, nondegeneracy, nontriviality, dimension or scalar
compatibility hypothesis on the original action. The acting ring can be
unital and still act by zero.

Use the exact integer-compatible action
`ρ = NonUnitalModule.toIntLinearEndHom (A := A) (V := V)` and the actual
canonical integer-linearization `a = f.toAddMonoidHom.toIntLinearMap`.
Integer scalars are the canonical scalars of the given additive group;
they are independent of the possibly-zero original action, including
when `A = ℤ`. The original law `f.map_smul` gives the commutation needed
by the existing generic `localizedAction a ρ`. Let that action be `σ`,
on the existing `EndomorphismLocalization.Localized a`. The source
unitized module is exactly `CompatibleUnitization.module ρ`, and the
target unitized module is exactly `CompatibleUnitization.module σ`.
Each is selected locally by `letI`; there is no global instance.

The private generic alias `actualLocalizedScalarModule` selects the
existing scalar module used by the generic actual localization. Its
body is `inferInstance` at a generic commutative coefficient ring. The
alias is installed locally before binding `σ`, so specialization to ℤ
retains that same module argument rather than selecting a different,
though mathematically equal, canonical integer dictionary. It creates
no new scalar action, ambient action or localization and is not a
public constructor.

## Conclusion and three closed targets

`AdditiveLocalizationStabilizationAt f` sets `a` as above and asserts
surjectivity of the existing `iota a`, together with a single `n : ℕ`
with `0 < n` and all three equalities

```text
ker(iota a) = ker(a^n)
ker(a^n) = ker((a^n)^2)
range(a^n) = range((a^n)^2).
```

All kernels and ranges here are actual integer submodules of the
original V. The same positive n occurs in each equality. This avoids
applying the current complex-specific `Stable` predicate to integers.
The target does not assume surjectivity, stability or a decomposition.

`UnitizedNoetherianSurjectivityStatement` requires only ordinary
`IsNoetherian U (Localized a)` for the actual unitized target action,
and concludes surjectivity of the actual canonical map. It has no
Noetherian source or ring hypothesis.

`UnitizedNoetherianStabilizationStatement` requires ordinary
`IsNoetherian U V` and `IsNoetherian U (Localized a)` for those two actual
unitized modules, and concludes `AdditiveLocalizationStabilizationAt f`.
It has no ring Noetherianity or finite-generation premise.

`UnitizedFiniteStabilizationStatement` requires exactly
`IsNoetherianRing U`, `Module.Finite U V` and
`Module.Finite U (Localized a)` for those same modules, and concludes
the same parameterized proposition. Ordinary ring Noetherianity here
is left Noetherianity of U's regular module; no commutativity is imposed.

`AdditiveLocalizationNoetherianStatements.{uA,uV}` is exactly the
conjunction of these three closed propositions in that order. All five
public declarations are transparent Prop-valued definitions. No target
is proved in this file.

## Derivation rationale

A future proof uses the automatic integer intertwiner, the existing
actual canonical/localized/inverse intertwiners, and their conversion by
`CompatibleUnitization.ofLinearIntertwiner` into ordinary U-linear maps.
The actual localized operator and inverse supply an automorphism of the
actual target module. The published fraction representation gives
power exhaustion; the actual canonical-map kernel is locally nilpotent.
Apply `NoetherianLocalizationCore.exhaustion_surjective` and
`NoetherianLocalizationCore.localization_core` to those maps. Equality
of their U-linear kernel/range submodules gives equality of the same
underlying sets for the original canonical integer-linear maps and
powers. Finite modules over a Noetherian ring supply both Noetherian
module instances for the third target. These are intended proof steps,
not additional premises or a proof implemented by this statement pair.

The complex-compatible Noetherian statement task
`699274ce-fd8e-4479-8659-02921d984da9` requires complex-linear data and
is distinct. Ordinary localization-stability statements require
Noetherianity over the localization coefficient ring itself. Here the
coefficient ring for localization is ℤ while the explicit Noetherian
hypotheses concern U; those earlier hypotheses cannot simply be
specialized to discharge these targets. Existing owners are preserved.

## Development checks

Worker 709 inspected all five complete unapplied declaration types and bodies.
They retain independent acting-ring and carrier universes, the original ambient
action, canonical integer scalars and linearization, the actual localized scalar
module, and exactly the source and target unitized modules described above.
The aggregate compiles and returns `Prop`; its inspected assumptions are only
`propext`, `Classical.choice` and `Quot.sound`.

Worker 735 repeated these checks in the pinned Lean service for this
submission. The aggregate and `AdditiveLocalizationStabilizationAt` compile with
no errors or warnings, report `statement_returns_prop: true` and level parameters
`uA uV`, and use only those three axioms. Explicitly elaborated bodies confirm:
`IsNoetherian U V` and `Module.Finite U V` use
`CompatibleUnitization.module ρ`; the `Localized a` hypotheses use
`CompatibleUnitization.module σ`; and the scalar module used by `iota a` and `σ`
is the generic Ore-localization module at coefficient ring ℤ. The elaborator
records the binding of `σ` as a non-dependent `have`. Since `σ` is used only
in the target module argument, this does not change the proposition.

Separate private diagnostics checked the converted canonical map with its exact
source and target unitized module arguments, the actual endomorphism and inverse,
their powers, kernel and range sets, and the resulting target automorphism.
Universe probes checked the closed declarations at both `(0,1)` and `(1,0)`.
A regression with `A = V = ℤ` and original zero action retained the canonical
integer-linear identity, sending one to one. Both the original and localized
ambient actions stayed zero, while the unitization's scalar coordinate retained
canonical integer scalars on each module. These checks prove only the stated
map and scalar coherence facts, and the diagnostic modules are excluded from
this pair. They are development evidence, not independent semantic acceptance
or proofs of the three targets.
