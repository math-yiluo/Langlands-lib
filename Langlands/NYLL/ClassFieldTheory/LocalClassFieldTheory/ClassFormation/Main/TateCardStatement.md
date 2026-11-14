# NYLL local class-field axiom for a specified generator: statement

Worker 111 adapts M157.005 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Main.lean`
(file SHA-256
`c376f249f260cf476149d2f99bf7a077848d3572322cbf2889d9cc7bc9fa1520`).
The readable pinned original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`,
registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The supplemental registration is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
There is no applicable NYLL entry in the Library's `notes/errata/`.

| Unit | Original declaration in `LocalClassFieldTheory` | Source lines (docstring through proof; statement) | Adapted declaration in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- | --- | --- |
| M157.005 | `localFieldUnits_tate_card_of_generator` | 99–108; 100–105 | `localFieldUnits_tate_card_of_generatorStatement` |

## Meaning

Let `L/K` be a finite Galois extension of nonarchimedean local fields, with
`L` carrying the valuation extending that of `K`, `𝒪[L]` integral over `𝒪[K]`
and finite as an `𝒪[K]`-module, and let `g : Gal(L/K)` be such that every
`sigma : Gal(L/K)` lies in `Subgroup.zpowers g`. The proposition is

```lean
Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) = Module.finrank K L ∧
  Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) = 1
```

that is, for Mathlib's integral representation `Rep.ofAlgebraAutOnUnits K L`
of `Gal(L/K)` on the units `Lˣ`, the degree-zero Tate cohomology group
`Ĥ⁰(Gal(L/K), Lˣ)` has cardinality `[L : K]` and the degree `-1` group
`Ĥ⁻¹(Gal(L/K), Lˣ)` has cardinality `1`. Here `Nat.card` is Mathlib's
cardinality with value `0` on infinite types; since `Module.finrank K L ≥ 1`
for the finite-dimensional field extension, the first conjunct implies that
`Ĥ⁰` is finite. This is the local class-field
axiom for a cyclic extension with a specified generator. `tateCohomology`,
`Rep.ofAlgebraAutOnUnits`, `Nat.card` and `Module.finrank` are Mathlib
declarations; the NYLL source uses them directly.

## Telescope

The source theorem takes its parameters from the section `variable` command
at lines 33–39, which binds `(K L : Type)`; the statement mentions `K` and
`L`, so every instance binder of that command is included. The adapted
definition writes this telescope explicitly, in source order and binder
kinds, followed by the theorem's own explicit binders (lines 101–102):

```lean
(K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
  [IsNonarchimedeanLocalField L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
  (g : Gal(L/K))
  (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g)
```

The fields are in `Type` (universe `0`), exactly as in the source, which has
no `universe` declaration; Mathlib's `tateCohomology` needs the coefficient
ring `ℤ` and the group `Gal(L/K)` in the same universe. The source file
contains no `omit` or `include` command. The binders `g` and `hg` do not occur
in the proposition; they are retained as in the source, and
`set_option linter.unusedVariables false in` is applied to the definition to
silence the linter. This option does not change the proposition.

## The omitted `letI`

The source statement (lines 103–105) is

```lean
letI := localFieldUnitsTateH0FiniteOfGenerator K L g hg
Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) = Module.finrank K L ∧
  Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) = 1
```

The `letI` installs, as a local instance, the proof of M157.004 that
`Finite (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0)`. No subterm of the
proposition consumes that instance: Mathlib's
`Nat.card (α : Type*) : ℕ` (`Mathlib.SetTheory.Cardinal.Finite`, line 41) has
no instance argument, and neither `tateCohomology`, `Rep.ofAlgebraAutOnUnits`
nor `Module.finrank` takes a finiteness instance on the Tate cohomology.
Because `letI` inlines its value only at its uses, the elaborated source
proposition is exactly the body written above, with no occurrence of
`localFieldUnitsTateH0FiniteOfGenerator`. The target therefore omits the
`letI` line and keeps lines 104–105 verbatim. Keeping it would require the
proof of M157.004, which is not part of this statement task. Revision 4 of
the host task (`04aeba8e-76d8-47d4-a1bb-ef1420764acf`) permits this
omission: its context removes the earlier gate of M157.005 on the M157.004
proof, provided the omission is recorded in this Markdown and no finiteness
or other hypothesis is added.

A focused draft check (not part of this module) confirmed this: a definition
with the same telescope, an extra hypothesis
`hfin : Finite (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0)` and the body
`letI := hfin` followed by lines 104–105 has, after opening its binders, a
body structurally equal (`Expr` equality) to the body of
`localFieldUnits_tate_card_of_generatorStatement` at the same binders, and
that body does not mention `hfin`. The check, run in a module importing this
one, with `sourceShaped` the definition just described, was

```lean
open Lean Meta in
#eval show MetaM Unit from do
  let v1 := (← getConstInfo ``sourceShaped).value!
  let v2 := (← getConstInfo
    ``Langlands.NYLL.LocalClassFieldTheory.localFieldUnits_tate_card_of_generatorStatement).value!
  lambdaTelescope v1 fun xs b1 => do
    let b2 := v2.beta xs.pop
    logInfo m!"structurally equal bodies: {b1 == b2}; \
      body mentions hfin: {b1.containsFVar xs.back!.fvarId!}; binders: {xs.size}"
```

and reported `structurally equal bodies: true; body mentions hfin: false;
binders: 20`.

## Modifications

- The namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`.
- The theorem becomes a `Prop`-valued `def` with the suffix `Statement`.
  Its body is the source statement without the inert leading `letI`, as
  explained above; the elaborated proposition is unchanged. The source proof
  (which uses `fieldUnits_tate_card_of_integerUnits_herbrand_eq_one` and the
  private theorems at lines 73–88) is not ported here; a proof of this target
  is separate `lean.proof@1` work.
- The section-variable telescope is written as explicit binders, so that no
  instance binder is dropped.
- The source imports (`Mathlib.SetTheory.Cardinal.Finite` and three NYLL
  class-formation modules) are replaced by the six Mathlib modules
  `Mathlib.FieldTheory.Galois.Basic`, `Mathlib.NumberTheory.LocalField.Basic`,
  `Mathlib.RepresentationTheory.Homological.TateCohomology.Basic`,
  `Mathlib.RepresentationTheory.Rep.Basic`,
  `Mathlib.RingTheory.Valuation.Extension` and
  `Mathlib.SetTheory.Cardinal.Finite`, which supply every constant in the
  telescope and target. No NYLL declaration occurs in this statement.
- Of the source's opening commands (lines 21–31), only
  `open scoped ValuativeRel` (for the `𝒪[K]` notation) is retained.
  `open CyclicCohomology`, `open LocalFieldTheory`,
  `open IsNonarchimedeanLocalField` and
  `open CyclicCohomology.ProfiniteCohomology.Herbrand` are omitted because the
  statement uses no name from these namespaces.
- The other declarations of the source module are not part of this module.
  M157.004 (`localFieldUnitsTateH0FiniteOfGenerator`) is published separately,
  as `localFieldUnitsTateH0FiniteOfGeneratorStatement` in
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Main.TateH0FiniteStatement`;
  M157.001 (`exists_localIntegerUnitsHerbrandDefinedAndEqOne`) is a separate
  unit of this task; the private theorems at lines 73–88 and the `IsCyclic`
  variants after line 109 are not listed units.
- The docstring is rewritten to describe the proposition and name the unit.

No hypothesis is added or removed, no proof is supplied and no instance is
declared. The copyright and author header is retained, followed by a
modification notice. The Apache-2.0 `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` in the Library remain applicable. This module states
the local class-field axiom for one cyclic extension; it proves nothing.
