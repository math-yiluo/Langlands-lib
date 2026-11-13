# Normalized valuation of a separable field norm: statement target

`Langlands.NYLL.LocalClassFieldTheory.v_normUnits_eq_residue_finrank_mul_of_isSeparableStatement`
concerns a finite separable extension `L / K` of nonarchimedean local fields
whose valuation on `L` extends that on `K` and in which `𝒪[L]` is the integral
closure of `𝒪[K]` in `L`. The proposition says that for a unit `x` of `L`, the
normalized valuation of its field norm `N_{L/K}(x)` equals the residue degree
`[𝓀[L] : 𝓀[K]]` times the normalized valuation of `x`. In Lean:

```lean
open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

attribute [local instance] FractionRing.liftAlgebra

def v_normUnits_eq_residue_finrank_mul_of_isSeparableStatement
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (x : Lˣ) : Prop :=
  v K (Additive.ofMul (normUnits K L x)) =
    (Module.finrank 𝓀[K] 𝓀[L] : Int) *
      v L (Additive.ofMul x)
```

This is the statement of source unit M162.019. Defining the proposition does not
prove it.

## Parameters and meaning

The declaration has universe parameters `u` and `v`, as in the source
(`K : Type u`, `L : Type v`). The parameters are:

| Binder | Kind | Meaning |
| --- | --- | --- |
| `K`, `L` | explicit, `Type u`, `Type v` | Base field and extension field |
| `[Field K]`, `[ValuativeRel K]`, `[TopologicalSpace K]` | instance-implicit | Field, valuative relation and topology on `K` |
| `[IsNonarchimedeanLocalField K]` | instance-implicit | `K` is a nonarchimedean local field (Mathlib class) |
| `[Field L]`, `[ValuativeRel L]`, `[TopologicalSpace L]`, `[IsNonarchimedeanLocalField L]` | instance-implicit | The same structures on `L` |
| `[Algebra K L]` | instance-implicit | The extension `K → L` |
| `[FiniteDimensional K L]` | instance-implicit | `L / K` is finite |
| `[Algebra.IsSeparable K L]` | instance-implicit | `L / K` is separable |
| `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]` | instance-implicit | The valuation of `L` extends that of `K` |
| `[IsIntegralClosure 𝒪[L] 𝒪[K] L]` | instance-implicit | `𝒪[L]` is the integral closure of `𝒪[K]` in `L` |
| `x : Lˣ` | explicit | A nonzero element of `L` |

`IsNonarchimedeanLocalField K` (`Mathlib/NumberTheory/LocalField/Basic.lean`,
line 45) says that the topology of `K` is the valuative topology, that `K` is
locally compact and that the valuative relation is nontrivial.
`Valuation.HasExtension vK vL` (`Mathlib/RingTheory/Valuation/Extension.lean`,
line 65) says that `vK` is equivalent to the pullback of `vL` along
`algebraMap K L`. Under it Mathlib makes `𝒪[L]` an `𝒪[K]`-algebra by restricting
`algebraMap K L` (line 119), and this algebra map is a local homomorphism
(lines 153–154), which induces the algebra structure `𝓀[K] → 𝓀[L]` on residue
fields. In the integral-closure hypothesis, `𝒪[K]` acts on `L` through `K` and
`𝒪[L]` acts on `L` by inclusion; both are Mathlib's subring algebra structures.
Under the scoped `ValuativeRel` notation
(`Mathlib/Topology/Algebra/Valued/ValuativeRel.lean`, lines 88–94), `𝒪[K]` is
`Valuation.integer (ValuativeRel.valuation K)` and `𝓀[K]` is
`IsLocalRing.ResidueField 𝒪[K]`.

The two published NYLL definitions in the conclusion are:

- `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v K :
  Additive Kˣ → Int` (source unit M128.001), the normalized integer valuation
  of a field unit. It transports the value group of `K` to `ℤₘ₀` through
  Mathlib's `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K` and takes
  the integer exponent of the nonzero value. `Additive.ofMul` views a unit as an
  element of `Additive Kˣ`.
- `Langlands.NYLL.LocalFieldTheory.normUnits K L : Lˣ →* Kˣ` (source unit
  M092.002), the field norm `Algebra.norm K` restricted to unit groups
  (`Units.map (Algebra.norm K)`).

So the proposition asserts `v_K(N_{L/K}(x)) = f(L / K) · v_L(x)` for every
unit `x` of `L`, where `f(L / K) = Module.finrank 𝓀[K] 𝓀[L]` is the residue
degree, cast to `Int`.

The file-level attribute `attribute [local instance] FractionRing.liftAlgebra`
is kept from the source (line 321). This statement does not use it: its
elaborated type contains no `FractionRing.liftAlgebra`. The attribute only
affects the elaboration of later declarations in the same file, and this file
has none.

## Original source and declaration map

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean`,
SHA-256 `b54bcd01a217ffc5fb905d410fe9ef64ebf87e5d7192509332cad827fc22c90e`.
The relevant lines are:

- the file-level local instance attribute at line 321;
- the docstring at lines 492–494;
- the theorem's statement at lines 495–508 and its proof from line 508.

The file opens `namespace LocalClassFieldTheory` (line 23), `LocalFieldTheory`
(line 25), `noncomputable section` (line 29), `scoped ValuativeRel` (line 33)
and `IsNonarchimedeanLocalField` (line 34), and declares `universe u v w`
(line 31). In the source, `v` is
`LocalFieldTheory.IsNonarchimedeanLocalField.v` (file
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`, line 29)
and `normUnits` is `LocalFieldTheory.normUnits` (file
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean`, line 33). The theorem lies
outside every `section` of the file, and no `variable` is in scope at this
point, so its binders are the whole telescope. `IsNonarchimedeanLocalField` is
Mathlib's class: NYLL declares no class of that name. The source statement is:

```lean
theorem v_normUnits_eq_residue_finrank_mul_of_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (x : Lˣ) :
    v K (Additive.ofMul (normUnits K L x)) =
      (Module.finrank 𝓀[K] 𝓀[L] : Int) *
        v L (Additive.ofMul x) := by
```

The retained original is in the project literature folder
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.v_normUnits_eq_residue_finrank_mul_of_isSeparable` (M162.019) | `Langlands.NYLL.LocalClassFieldTheory.v_normUnits_eq_residue_finrank_mul_of_isSeparableStatement` |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v` (M128.001, used) | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v` (published) |
| `LocalFieldTheory.normUnits` (M092.002, used) | `Langlands.NYLL.LocalFieldTheory.normUnits` (published) |

Row M162.019 of the published partition
[`notes/reuse/nyll-public-port/m145-m168.md`](../../../../../../../notes/reuse/nyll-public-port/m145-m168.md)
reserves `Langlands.NYLL.LocalClassFieldTheory.v_normUnits_eq_residue_finrank_mul_of_isSeparable`
for the later proof. Section 3 of
[`notes/reuse/nyll-public-port-plan.md`](../../../../../../../notes/reuse/nyll-public-port-plan.md)
gives the `Statement` suffix for the target. The partition's predecessor
`M162.018.END` is scheduling order only: the statement mentions no other source
declaration of this module. No NYLL erratum for this module was found in the
current Library's `notes/`.

## Imports and modification record

The direct imports are:

- the source's two Mathlib imports, `Mathlib.FieldTheory.SeparableClosure` and
  `Mathlib.RingTheory.Ideal.Norm.RelNorm`. They supply `Algebra.IsSeparable`,
  `IsIntegralClosure`, `Module.finrank` and `FractionRing.liftAlgebra`;
- `Mathlib.RingTheory.Valuation.Extension`, for `Valuation.HasExtension` and
  the algebra structure `𝒪[K] → 𝒪[L]` with its local-homomorphism instance;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.Definitions`,
  the published module defining `v`. Through its import of
  `Mathlib.NumberTheory.LocalField.Basic` it also supplies the class
  `IsNonarchimedeanLocalField` and the scoped notation `𝒪[·]`, `𝓀[·]`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`, the
  published module defining `normUnits`.

The source's four NYLL imports are replaced by these. Every transitive import
lies in the approved Mathlib environment or the published Library.

The adaptation makes these changes:

- it moves the theorem's telescope and conclusion into the Prop-valued
  definition above. Binder order, binder kinds, binder names, universes, the
  (here unused) local instance attribute and the conclusion are unchanged;
- it resolves `v` and `normUnits` to the published adaptations by opening
  `Langlands.NYLL.LocalFieldTheory` and
  `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField`, which replace the
  source's opens of `LocalFieldTheory` and `IsNonarchimedeanLocalField`;
- it omits the source proof and every other declaration of the module;
- it puts the definition in the namespace `Langlands.NYLL.LocalClassFieldTheory`
  and keeps the source's `noncomputable section`.

The source docstring is retained. The Lean header records these changes with
Worker 85's dated modification note.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection reports a definition
whose type ends in `Prop` (`statement_returns_prop: true`), with level
parameters `u`, `v` and only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`. This development check is not independent acceptance.

## Boundary and license

This file defines the proposition only. The theorem
`Langlands.NYLL.LocalClassFieldTheory.v_normUnits_eq_residue_finrank_mul_of_isSeparable`
and its proof need a separate proof task once this target is in the Library.
The source proof (lines 508–536) writes `x = a · ϖ ^ n`, where `ϖ` is the
source's inverse integer-ring uniformizer field unit of `L` (normalized value
`1`), `n = v L x` and `a` is a unit of `𝒪[L]`. It takes norms, uses that
integral units have normalized value `0`, and applies the source lemma M162.018
for the normalized value of the norm of `ϖ`. Several of these source
declarations are not yet in the Library, and a proof may follow that route or
another.

The Lean file keeps the original copyright and author header unchanged:
Copyright (c) 2026 Naganori Yamaguchi; Authors: Naganori Yamaguchi (assisted
by OpenAI Codex). It remains under Apache-2.0. The already-published
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are reused unchanged and
included through `repository_paths`. Their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. Worker 85
adapted this unit directly from the pinned original; no other project worker
supplied code.
