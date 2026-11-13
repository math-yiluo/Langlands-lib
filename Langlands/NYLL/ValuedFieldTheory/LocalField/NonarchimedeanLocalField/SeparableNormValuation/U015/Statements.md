# Separability of the fraction fields of valuation integer rings: statement target

`Langlands.NYLL.LocalClassFieldTheory.fractionRing_integerRing_isSeparableStatement`
concerns a separable field extension `L / K` in which the canonical valuation of
`L` extends that of `K`. The proposition says that the fraction field of the
integer ring `𝒪[L]` is separable over the fraction field of `𝒪[K]`. In Lean:

```lean
open scoped ValuativeRel

attribute [local instance] FractionRing.liftAlgebra

def fractionRing_integerRing_isSeparableStatement
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L]
    [Algebra K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)] : Prop :=
  Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing 𝒪[L])
```

This is the statement of source unit M162.015. Defining the proposition does not
prove it.

## Parameters and meaning

The declaration has universe parameters `u` and `v`, as in the source
(`K : Type u`, `L : Type v`). The parameters are:

| Binder | Kind | Meaning |
| --- | --- | --- |
| `K`, `L` | explicit, `Type u`, `Type v` | Base field and extension field |
| `[Field K]`, `[Field L]` | instance-implicit | Field structures |
| `[ValuativeRel K]`, `[ValuativeRel L]` | instance-implicit | Mathlib valuative relations; each determines a canonical valuation `ValuativeRel.valuation` |
| `[Algebra K L]` | instance-implicit | The extension `K → L` |
| `[Algebra.IsSeparable K L]` | instance-implicit | `L / K` is separable |
| `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]` | instance-implicit | The valuation of `L` extends that of `K` |

`Valuation.HasExtension vK vL` (`Mathlib/RingTheory/Valuation/Extension.lean`,
line 65) says that `vK` is equivalent to the pullback of `vL` along
`algebraMap K L`. Under it Mathlib makes `𝒪[L]` an algebra over `𝒪[K]` by
restricting `algebraMap K L` (`Valuation.HasExtension.instAlgebraInteger`,
line 119). Under the scoped `ValuativeRel` notation,
`𝒪[K]` is `Valuation.integer (ValuativeRel.valuation K)`, the subring of
elements of valuation at most one
(`Mathlib/Topology/Algebra/Valued/ValuativeRel.lean`, line 88).

The algebra structure `Frac 𝒪[K] → Frac 𝒪[L]` in the conclusion is not a
hypothesis. It is Mathlib's `FractionRing.liftAlgebra 𝒪[K] (FractionRing 𝒪[L])`
(`Mathlib/RingTheory/Localization/FractionRing.lean`, line 769), the unique
extension of the composite `𝒪[K] → 𝒪[L] → Frac 𝒪[L]` to the fraction field of
`𝒪[K]`. As in the source, the file registers `FractionRing.liftAlgebra` as a
local instance; this statement is its only user here.

So the proposition asserts that `Frac 𝒪[L] / Frac 𝒪[K]` is separable whenever
`L / K` is separable and the valuation of `L` extends that of `K`. Mathematically
`Frac 𝒪[K]` and `Frac 𝒪[L]` are copies of `K` and `L`, so this is a transport of
the separability hypothesis to the canonical fraction-field models. No
finiteness, discreteness, completeness, topology or local-field hypothesis is
assumed.

## Original source and declaration map

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean`,
SHA-256 `b54bcd01a217ffc5fb905d410fe9ef64ebf87e5d7192509332cad827fc22c90e`.
The relevant lines are:

- the file-level local instance attribute at line 321;
- the docstring at lines 371–372;
- the theorem's statement at lines 373–380 and its proof at lines 380–387.

The file opens `namespace LocalClassFieldTheory` (line 23) and
`noncomputable section` (line 29), declares `universe u v w` (line 31) and opens
`scoped ValuativeRel` (line 33). The theorem lies outside every `section` of the
file, and no `variable` is in scope at this point, so its binders are the whole
telescope. The source lines that make up the statement are:

```lean
attribute [local instance] FractionRing.liftAlgebra

theorem fractionRing_integerRing_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L]
    [Algebra K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)] :
    Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing 𝒪[L]) := by
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
| `LocalClassFieldTheory.fractionRing_integerRing_isSeparable` (M162.015) | `Langlands.NYLL.LocalClassFieldTheory.fractionRing_integerRing_isSeparableStatement` |

Row M162.015 of the published partition
[`notes/reuse/nyll-public-port/m145-m168.md`](../../../../../../../notes/reuse/nyll-public-port/m145-m168.md)
reserves `Langlands.NYLL.LocalClassFieldTheory.fractionRing_integerRing_isSeparable`
for the later proof. Section 3 of
[`notes/reuse/nyll-public-port-plan.md`](../../../../../../../notes/reuse/nyll-public-port-plan.md)
gives the `Statement` suffix for the target. The partition's predecessor
`M162.014.END` is scheduling order only: the statement mentions no earlier
source declaration. No NYLL erratum for this module was found in the current
Library's `notes/`.

## Imports and modification record

The direct imports are:

- the source's two Mathlib imports, `Mathlib.FieldTheory.SeparableClosure` and
  `Mathlib.RingTheory.Ideal.Norm.RelNorm`. They supply `Algebra.IsSeparable`,
  `FractionRing` and `FractionRing.liftAlgebra`;
- `Mathlib.RingTheory.Valuation.Extension`, for `Valuation.HasExtension` and
  the algebra structure `𝒪[K] → 𝒪[L]`;
- `Mathlib.Topology.Algebra.Valued.ValuativeRel`, for `ValuativeRel`,
  `ValuativeRel.valuation` and the scoped notation `𝒪[·]`.

In the source these Mathlib declarations arrive through the four NYLL imports,
which are not otherwise needed by this statement and are dropped. Every
transitive import lies in the approved Mathlib environment.

The adaptation makes these changes:

- it moves the theorem's telescope and conclusion into the Prop-valued
  definition above. Binder order, binder kinds, binder names, universes, the
  local instance attribute and the conclusion are unchanged;
- it omits the source proof and every other declaration of the module;
- it replaces the NYLL imports by the two Mathlib imports listed above;
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
`Langlands.NYLL.LocalClassFieldTheory.fractionRing_integerRing_isSeparable` and
its proof need a separate proof task once this target is in the Library. The
source proof (lines 380–387) applies `Algebra.IsSeparable.of_equiv_equiv` to the
inverses of the canonical isomorphisms `FractionRing.algEquiv 𝒪[K] K` and
`FractionRing.algEquiv 𝒪[L] L`. It checks the compatibility square with
`IsFractionRing.algEquiv_commutes`. That route needs `K` and `L` to be fraction
fields of `𝒪[K]` and `𝒪[L]` (`IsFractionRing` instances), which the source
proof finds through its imports. A proof may follow that route or another.

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
