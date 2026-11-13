# Normalized valuation of the norm of a prime element: statement targets

This module defines two propositions about a finite separable extension
`L / K` of nonarchimedean local fields. The valuation on `L` must extend the one
on `K`, and `𝒪[L]` must be the integral closure of `𝒪[K]` in `L`. Let `ϖ_L` be
the chosen uniformizer of `L` viewed as a unit, and `f = [𝓀[L] : 𝓀[K]]` the
residue degree. The propositions are:

- `Langlands.NYLL.LocalClassFieldTheory.v_normUnits_integerRingUniformizerFieldUnit_of_isSeparableStatement`
  (source unit M162.017): `v_K(N_{L/K}(ϖ_L)) = -f`;
- `Langlands.NYLL.LocalClassFieldTheory.v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparableStatement`
  (source unit M162.018): `v_K(N_{L/K}(ϖ_L⁻¹)) = f`.

In Lean:

```lean
open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

attribute [local instance] FractionRing.liftAlgebra

def v_normUnits_integerRingUniformizerFieldUnit_of_isSeparableStatement
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] : Prop :=
  v K (Additive.ofMul
      (normUnits K L (integerRingUniformizerFieldUnit L))) =
    -(Module.finrank 𝓀[K] 𝓀[L] : Int)

def v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparableStatement
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] : Prop :=
  v K (Additive.ofMul
      (normUnits K L (inverseIntegerRingUniformizerFieldUnit L))) =
    (Module.finrank 𝓀[K] 𝓀[L] : Int)
```

These are the statements of source units M162.017 and M162.018. Defining the
propositions does not prove them.

## Parameters and meaning

Both declarations have universe parameters `u` and `v`, as in the source
(`K : Type u`, `L : Type v`), and the same telescope:

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

`IsNonarchimedeanLocalField K` (`Mathlib/NumberTheory/LocalField/Basic.lean`)
says that the topology of `K` is the valuative topology, that `K` is locally
compact and that the valuative relation is nontrivial.
`Valuation.HasExtension vK vL` (`Mathlib/RingTheory/Valuation/Extension.lean`)
says that `vK` is equivalent to the pullback of `vL` along `algebraMap K L`.
Under it Mathlib makes `𝒪[L]` an `𝒪[K]`-algebra by restricting
`algebraMap K L`, and this algebra map is a local homomorphism, which induces
the algebra structure `𝓀[K] → 𝓀[L]` on residue fields used by
`Module.finrank 𝓀[K] 𝓀[L]`. In the integral-closure hypothesis, `𝒪[K]` acts on
`L` through `K`, and `𝒪[L]` acts on `L` by inclusion; both are Mathlib's subring
algebra structures. Under the scoped `ValuativeRel` notation
(`Mathlib/Topology/Algebra/Valued/ValuativeRel.lean`), `𝒪[K]` is
`Valuation.integer (ValuativeRel.valuation K)` and `𝓀[K]` is
`IsLocalRing.ResidueField 𝒪[K]`.

The four published NYLL definitions in the conclusions are:

- `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v K :
  Additive Kˣ → Int` (source unit M128.001), the normalized integer valuation
  of a field unit. It transports the value group of `K` to `ℤₘ₀` through
  Mathlib's `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K` and takes
  the integer exponent of the nonzero value. With this convention a prime
  element of `K` has value `-1`, not `1`. The Library note
  `notes/reuse/nyll-finite-local-reciprocity-audit.md`, section 2.3, records
  that NYLL's `v` is minus the usual order. `Additive.ofMul` views a unit as an
  element of `Additive Kˣ`.
- `Langlands.NYLL.LocalFieldTheory.normUnits K L : Lˣ →* Kˣ` (source unit
  M092.002), the field norm `Algebra.norm K` restricted to unit groups.
- `Langlands.NYLL.LocalFieldTheory.integerRingUniformizerFieldUnit L : Lˣ`
  (source unit M133.007), the chosen uniformizer
  `chosenIntegerRingUniformizer L` of `𝒪[L]` (an irreducible element chosen by
  `Classical.choose`), viewed as a unit of `L`.
- `Langlands.NYLL.LocalFieldTheory.inverseIntegerRingUniformizerFieldUnit L : Lˣ`
  (source unit M133.009), the inverse of that unit.

So the first proposition asserts that the norm of a prime element of `L` has
NYLL-normalized value `-f` in `K`. Equivalently, its order in `K` is `f`. The
second asserts that the norm of the inverse prime element has value `f`. The
residue degree `Module.finrank 𝓀[K] 𝓀[L]` is a natural number cast to `Int`;
the first conclusion negates the cast.

The file-level attribute `attribute [local instance] FractionRing.liftAlgebra`
is kept from the source (line 321). Neither statement uses it. The attribute
only affects the elaboration of later declarations in the same file, and the
Prop-valued definitions here contain no `FractionRing` term.

## Original source and declaration map

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean`,
SHA-256 `b54bcd01a217ffc5fb905d410fe9ef64ebf87e5d7192509332cad827fc22c90e`.
The relevant lines are:

- the file-level local instance attribute at line 321;
- M162.017: docstring at lines 412–414, statement at lines 415–427, proof
  from line 427 to line 471;
- M162.018: docstring at lines 473–474, statement at lines 475–487, proof at
  lines 487–490.

The file opens `namespace LocalClassFieldTheory` (line 23) and
`open LocalFieldTheory` (line 25). It then opens a `noncomputable section`
(line 29), declares `universe u v w` (line 31) and opens
`scoped BigOperators ValuativeRel` (line 33) and `IsNonarchimedeanLocalField`
(line 34). In the source, `v` is `LocalFieldTheory.IsNonarchimedeanLocalField.v`
(file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`,
line 29). `normUnits` is `LocalFieldTheory.normUnits` (file
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean`, line 33). The two unit
definitions are `LocalFieldTheory.integerRingUniformizerFieldUnit` and
`LocalFieldTheory.inverseIntegerRingUniformizerFieldUnit` (file
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean`,
lines 74 and 96). Both theorems lie outside every `section` of the file, and
no `variable` is in scope at that point, so their binders are the whole
telescope. The source statements are:

```lean
theorem v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    v K (Additive.ofMul
        (normUnits K L (integerRingUniformizerFieldUnit L))) =
      -(Module.finrank 𝓀[K] 𝓀[L] : Int) := by

theorem v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    v K (Additive.ofMul
        (normUnits K L (inverseIntegerRingUniformizerFieldUnit L))) =
      (Module.finrank 𝓀[K] 𝓀[L] : Int) := by
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
| `LocalClassFieldTheory.v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable` (M162.017) | `Langlands.NYLL.LocalClassFieldTheory.v_normUnits_integerRingUniformizerFieldUnit_of_isSeparableStatement` |
| `LocalClassFieldTheory.v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparable` (M162.018) | `Langlands.NYLL.LocalClassFieldTheory.v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparableStatement` |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v` (M128.001, used) | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v` (published) |
| `LocalFieldTheory.normUnits` (M092.002, used) | `Langlands.NYLL.LocalFieldTheory.normUnits` (published) |
| `LocalFieldTheory.integerRingUniformizerFieldUnit` (M133.007, used) | `Langlands.NYLL.LocalFieldTheory.integerRingUniformizerFieldUnit` (published) |
| `LocalFieldTheory.inverseIntegerRingUniformizerFieldUnit` (M133.009, used) | `Langlands.NYLL.LocalFieldTheory.inverseIntegerRingUniformizerFieldUnit` (published) |

Rows M162.017 and M162.018 of the published partition
[`notes/reuse/nyll-public-port/m145-m168.md`](../../../../../../../notes/reuse/nyll-public-port/m145-m168.md)
reserve the names without the `Statement` suffix for the later proofs.
Section 3 of
[`notes/reuse/nyll-public-port-plan.md`](../../../../../../../notes/reuse/nyll-public-port-plan.md)
gives the `Statement` suffix for targets. The partition's predecessors
`M162.016.END` and `M162.017.END` are scheduling order only. Neither statement
mentions another source declaration of this module. The Library's
`notes/errata/` has no NYLL entry.

## Imports and modification record

The direct imports are:

- the source's two Mathlib imports, `Mathlib.FieldTheory.SeparableClosure` and
  `Mathlib.RingTheory.Ideal.Norm.RelNorm`. They supply `Algebra.IsSeparable`,
  `IsIntegralClosure`, `Module.finrank` and `FractionRing.liftAlgebra`;
- `Mathlib.RingTheory.Valuation.Extension`, for `Valuation.HasExtension` and
  the algebra structure `𝒪[K] → 𝒪[L]` with its local-homomorphism instance;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.Definitions`,
  the published module defining `v`. Through its import of
  `Mathlib.NumberTheory.LocalField.Basic`, it also supplies the class
  `IsNonarchimedeanLocalField` and the scoped notation `𝒪[·]`, `𝓀[·]`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`, the
  published module defining `normUnits`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U007.Definitions`,
  the published module defining the two uniformizer units.

The source's four NYLL imports are replaced by these. Every transitive import
lies in the approved Mathlib environment or the published Library.

The adaptation makes these changes:

- it moves each theorem's telescope and conclusion into the Prop-valued
  definition above. Binder order, binder kinds, binder names, universes, the
  (here unused) local instance attribute and the conclusions are unchanged;
- it resolves `v`, `normUnits` and the two unit definitions to the published
  adaptations by opening `Langlands.NYLL.LocalFieldTheory` and
  `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField`. These replace
  the source's opens of `LocalFieldTheory` and `IsNonarchimedeanLocalField`;
- it omits the source proofs and every other declaration of the module;
- it puts the definitions in the namespace
  `Langlands.NYLL.LocalClassFieldTheory` and keeps the source's
  `noncomputable section`.

The source docstrings are retained. The Lean header records these changes with
Worker 85's dated modification note.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection of each declaration
reports a definition whose type ends in `Prop` (`statement_returns_prop: true`),
with level parameters `u`, `v` and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. This development check is not independent
acceptance.

## Boundary and license

This file defines the propositions only. The theorems
`Langlands.NYLL.LocalClassFieldTheory.v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable`
and
`Langlands.NYLL.LocalClassFieldTheory.v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparable`
need separate proof tasks once these targets are in the Library.

The source proof of M162.017 (lines 427–471) works with ideals. The norm of
the ideal generated by `ϖ_L` is the relative norm of `𝓂[L]` (source M133.006),
which equals `𝓂[K] ^ f` (source M162.016), which is generated by `ϖ_K ^ f`
(source M133.022). So `N(ϖ_L) = u · ϖ_K ^ f` for an integral unit `u`. Taking
`v` of both sides uses `v_mul`, `v_pow`, integral units having value `0`, and
`v(ϖ_K) = -1` (source M128.004/.008/.019 and M133.018). The source proof of
M162.018 rewrites with `map_inv` and `v_inv` (source M128.006) and applies
M162.017. A proof may follow that route or another.

The Lean file keeps the original copyright and author header unchanged:
Copyright (c) 2026 Naganori Yamaguchi; Authors: Naganori Yamaguchi (assisted
by OpenAI Codex). It remains under Apache-2.0. The already-published
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are reused unchanged and
included through `repository_paths`. Their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. Worker 85
adapted these units directly from the pinned original; no other project worker
supplied code.
