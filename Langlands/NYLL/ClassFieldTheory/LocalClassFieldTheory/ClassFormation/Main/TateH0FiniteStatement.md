# NYLL finiteness of unit Tate `H⁰` for a cyclic local extension: statement

Worker 111 adapts M157.004 from Naganori Yamaguchi,
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
| M157.004 | `localFieldUnitsTateH0FiniteOfGenerator` | 90–97; 92–95 | `localFieldUnitsTateH0FiniteOfGeneratorStatement` |

## Meaning

Let `L/K` be a finite Galois extension of nonarchimedean local fields, with
`L` carrying the valuation extending that of `K`, `𝒪[L]` integral over `𝒪[K]`
and finite as an `𝒪[K]`-module, and let `g : Gal(L/K)` be such that every
`sigma : Gal(L/K)` lies in `Subgroup.zpowers g`. The proposition is

```lean
Finite (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0)
```

that is, the degree-zero Tate cohomology group `Ĥ⁰(Gal(L/K), Lˣ)` of
Mathlib's integral representation of `Gal(L/K)` on the units `Lˣ`
(`Rep.ofAlgebraAutOnUnits K L`, the `ℤ`-linearisation of the natural
multiplicative action) is finite. Both `tateCohomology` and
`Rep.ofAlgebraAutOnUnits` are Mathlib declarations; the NYLL source uses them
directly.

## Telescope

The source theorem takes its parameters from the section `variable` command
at lines 33–39, which binds `(K L : Type)`; the statement mentions `K` and
`L`, so every instance binder of that command is included. The adapted
definition writes this telescope explicitly, in source order and binder
kinds, followed by the theorem's own explicit binders (lines 93–94):

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
ring `ℤ` and the group `Gal(L/K)` in the same universe. The source
file contains no `omit` or `include` command. The body is copied verbatim
from source line 95. The binders `g` and `hg` do not occur in the
proposition; they are retained as in the source, and
`set_option linter.unusedVariables false in` is applied to the definition to
silence the linter. This option does not change the proposition.

## Modifications

- The namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`.
- The theorem becomes a `Prop`-valued `def` with the suffix `Statement`
  whose body is exactly the source statement. The source proof (which uses
  `unitsTateH0FiniteOfIntegerUnitsHerbrand` and the private witness
  `localIntegerUnitsHerbrandDefined`) is not ported here; a proof of this
  target is separate `lean.proof@1` work.
- The section-variable telescope is written as explicit binders, so that no
  instance binder is dropped.
- The source imports (`Mathlib.SetTheory.Cardinal.Finite` and three NYLL
  class-formation modules) are replaced by the five Mathlib modules
  `Mathlib.FieldTheory.Galois.Basic`, `Mathlib.NumberTheory.LocalField.Basic`,
  `Mathlib.RepresentationTheory.Homological.TateCohomology.Basic`,
  `Mathlib.RepresentationTheory.Rep.Basic` and
  `Mathlib.RingTheory.Valuation.Extension`, which supply every constant in
  the telescope and target. No NYLL declaration occurs in this statement.
- Of the source's opening commands (lines 21–31), only
  `open scoped ValuativeRel` (for the `𝒪[K]` notation) is retained.
  `open CyclicCohomology`, `open LocalFieldTheory`,
  `open IsNonarchimedeanLocalField` and
  `open CyclicCohomology.ProfiniteCohomology.Herbrand` are omitted because the
  statement uses no name from these namespaces.
- The other declarations of the source module are not part of this module.
  M157.001 (`exists_localIntegerUnitsHerbrandDefinedAndEqOne`) and M157.005
  (`localFieldUnits_tate_card_of_generator`) are separate units of this task;
  the private theorems at lines 73–88 and the `IsCyclic` variants after
  line 109 are not listed units.
- The docstring is rewritten to describe the proposition and name the unit.

No hypothesis is added or removed, no proof is supplied and no instance is
declared. The copyright and author header is retained, followed by a
modification notice. The Apache-2.0 `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` in the Library remain applicable. This statement is
a finiteness target only; it proves no class-formation or reciprocity
theorem.
