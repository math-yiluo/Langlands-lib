# NYLL integer-unit Herbrand witness of the local class-field axiom: statement

Worker 111 adapts M157.001 from Naganori Yamaguchi,
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
| M157.001 | `exists_localIntegerUnitsHerbrandDefinedAndEqOne` | 41–69; 43–50 | `exists_localIntegerUnitsHerbrandDefinedAndEqOneStatement` |

## Meaning

Let `L/K` be a finite Galois extension of nonarchimedean local fields, with
`L` carrying the valuation extending that of `K`, `𝒪[L]` the integral closure
of `𝒪[K]` in `L` and finite as an `𝒪[K]`-module, and let `g : Gal(L/K)` be such
that every `sigma : Gal(L/K)` lies in `Subgroup.zpowers g`. Let `Gal(L/K)` act
on the integer units `𝒪[L]ˣ` by
`galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L`, the
action induced by restricting automorphisms to the integral closure. The
proposition is

```lean
letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
∃ hU : HerbrandQuotientDefined (Gal(L / K)) 𝒪[L]ˣ g,
  @herbrandQuotient (Gal(L / K)) 𝒪[L]ˣ _ _ _
    (galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L)
    g hU.1 hU.2 = 1
```

that is, for this action both multiplicative low-degree Herbrand groups
`HerbrandH0 (Gal(L/K)) 𝒪[L]ˣ = (𝒪[L]ˣ)^G / N_G(𝒪[L]ˣ)` and
`HerbrandHMinusOne (Gal(L/K)) 𝒪[L]ˣ g = ker N_G / (g - 1)(𝒪[L]ˣ)` are finite
(`HerbrandQuotientDefined` is the conjunction of these two `Finite`
propositions), and with these finiteness witnesses the Herbrand quotient
`#H⁰ / #H⁻¹ ∈ ℚ` equals `1`. The existential is over the proof `hU` of a
proposition, so the statement is equivalent to finiteness of both groups
together with equality of their cardinalities. The source proof chooses a
normal-basis level large enough for three earlier class-formation results.
That proof is not part of this statement.

## Telescope

The source theorem takes its parameters from the section `variable` command
at lines 33–39, which binds `(K L : Type)`; the statement mentions `K` and
`L`, so every instance binder of that command is included. The adapted
definition writes this telescope explicitly, in source order and binder
kinds, followed by the theorem's own explicit binders (lines 44–45):

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
no `universe` declaration. The source file contains no `omit` or `include`
command. The binder `hg` does not occur in the proposition; it is retained as
in the source, and `set_option linter.unusedVariables false in` is applied to
the definition to silence the linter. This option does not change the
proposition.

## Statement body

The body is the source statement (lines 46–50), unchanged. The leading
`letI` installs the integer-unit action as a local instance. Unlike the inert
`letI` of M157.005, this one is used: it supplies the
`MulDistribMulAction (Gal(L / K)) 𝒪[L]ˣ` instance argument of
`HerbrandQuotientDefined`, and so of the `hU.1` and `hU.2` finiteness
witnesses. `@herbrandQuotient` receives the same action explicitly, as in the
source. The three `_` placeholders are the `Group`, `Fintype` and `CommGroup`
instances of `Gal(L / K)` and `𝒪[L]ˣ`. Lean elaborates them by instance search
from Mathlib, as in the source.

## Dependencies

- `Langlands.NYLL.LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure`
  (source M140, `ClassFormation/Valuation/Integer.lean`), published in
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.IntegerDefinitions`.
- `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandQuotientDefined`
  (M119.001, source `GaloisCohomology/Cyclic/Herbrand/HerbrandFiniteness.lean`
  line 38), published in
  `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness.Definitions`.
  It takes `G` and `A` explicitly, followed by the instance binders
  `[Group G] [Fintype G] [CommGroup A] [MulDistribMulAction G A]` and `σ : G`.
- `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient`
  (M118.001, source `GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Core.lean`
  line 37), published in
  `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core.Definitions`.
  Its telescope is `{G} {A} [Group G] [Fintype G] [CommGroup A]
  [MulDistribMulAction G A] (σ : G) [Finite (HerbrandH0 G A)]
  [Finite (HerbrandHMinusOne G A σ)]`, as in the source, so the explicit
  application `@herbrandQuotient (Gal(L / K)) 𝒪[L]ˣ _ _ _ action g hU.1 hU.2`
  of the source applies to it with the same arguments.
- These are defined in terms of
  `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0` and
  `HerbrandHMinusOne` (M113.028/029), published in
  `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.HerbrandQuotients.Definitions`.

## Modifications

- The namespace `LocalClassFieldTheory` becomes
  `Langlands.NYLL.LocalClassFieldTheory`.
- The theorem becomes a `Prop`-valued `def` with the suffix `Statement`,
  whose body is the source statement. The source proof (lines 51–69) is not
  ported. It uses `exists_chosenNormalBasisPrincipalUnitSubgroup`,
  `exists_chosenNormalBasisPrincipalUnit_herbrand_subsingleton` and
  `exists_integerUnits_herbrandQuotient_eq_one_of_large_chosenNormalBasisLevel`.
  A proof of this target is separate `lean.proof@1` work.
- The section-variable telescope is written as explicit binders, so that no
  instance binder is dropped.
- The source imports (`Mathlib.SetTheory.Cardinal.Finite` and three NYLL
  class-formation modules) are replaced by three published Library modules
  and three Mathlib modules. The Library modules are
  `ClassFormation.Valuation.IntegerDefinitions`,
  `HerbrandFiniteness.Definitions` and `HerbrandLowDegree.Core.Definitions`,
  the first three items under Dependencies. The module of `HerbrandH0` and
  `HerbrandHMinusOne` comes in through the last two. The Mathlib modules are
  `Mathlib.FieldTheory.Galois.Basic`, `Mathlib.NumberTheory.LocalField.Basic`
  and `Mathlib.RingTheory.Valuation.Extension`. Together they supply every
  constant in the telescope and target.
- Of the source's opening commands (lines 21–31), `open scoped ValuativeRel`
  (for the `𝒪[K]` notation) and
  `open CyclicCohomology.ProfiniteCohomology.Herbrand`, prefixed to
  `open Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand` (for
  `HerbrandQuotientDefined` and `herbrandQuotient`), are retained.
  `open CyclicCohomology`, `open LocalFieldTheory` and
  `open IsNonarchimedeanLocalField` are omitted because the statement uses no
  other name from these namespaces.
- The other declarations of the source module are not part of this module.
  M157.004 and M157.005 are published separately in the sibling modules
  `Main.TateH0FiniteStatement` and `Main.TateCardStatement`. The private
  theorems at lines 73–88 and the `IsCyclic` variants after line 109 are not
  listed units.
- The docstring is rewritten to describe the proposition and name the unit.

No hypothesis is added or removed, no proof is supplied and no instance is
declared. The copyright and author header is retained, followed by a
modification notice. The Apache-2.0 `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` in the Library remain applicable. This module states
the integer-unit Herbrand input to the local class-field axiom; it proves
nothing.
