# Relative norm of the maximal ideal of a local-field extension: statement target

`Langlands.NYLL.LocalClassFieldTheory.relNorm_maximalIdeal_eq_pow_residue_finrankStatement`
concerns a finite separable extension `L / K` of nonarchimedean local fields
whose valuation on `L` extends that on `K` and whose integer ring `𝒪[L]` is a
finite `𝒪[K]`-module. The proposition says that the relative ideal norm of the
maximal ideal of `𝒪[L]` is the maximal ideal of `𝒪[K]` raised to the residue
degree `[𝓀[L] : 𝓀[K]]`. In Lean:

```lean
open scoped ValuativeRel

attribute [local instance] FractionRing.liftAlgebra

def relNorm_maximalIdeal_eq_pow_residue_finrankStatement
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] : Prop :=
  Ideal.relNorm 𝒪[K] (𝓂[L] : Ideal 𝒪[L]) =
    (𝓂[K] : Ideal 𝒪[K]) ^ Module.finrank 𝓀[K] 𝓀[L]
```

This is the statement of source unit M162.016. Defining the proposition does not
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
| `[Module.Finite 𝒪[K] 𝒪[L]]` | instance-implicit | `𝒪[L]` is a finitely generated `𝒪[K]`-module |

`IsNonarchimedeanLocalField K` (`Mathlib/NumberTheory/LocalField/Basic.lean`,
line 45) says that the topology of `K` is the valuative topology, that `K` is
locally compact and that the valuative relation is nontrivial. Mathlib then
makes `𝒪[K]` a discrete valuation ring (line 108), hence a Dedekind domain.
`Valuation.HasExtension vK vL` (`Mathlib/RingTheory/Valuation/Extension.lean`,
line 65) says that `vK` is equivalent to the pullback of `vL` along
`algebraMap K L`. Under it Mathlib makes `𝒪[L]` an algebra over `𝒪[K]` by
restricting `algebraMap K L` (line 119), and this algebra map is a local
homomorphism (`Valuation.HasExtension.instIsLocalHomValuationInteger`,
lines 153–154). The residue fields `𝓀[K]`, `𝓀[L]` are therefore related
by Mathlib's induced algebra structure on residue fields.

Under the scoped `ValuativeRel` notation
(`Mathlib/Topology/Algebra/Valued/ValuativeRel.lean`, lines 88–94):

- `𝒪[K]` is `Valuation.integer (ValuativeRel.valuation K)`, the ring of integers;
- `𝓂[K]` is `IsLocalRing.maximalIdeal 𝒪[K]`, its maximal ideal;
- `𝓀[K]` is `IsLocalRing.ResidueField 𝒪[K]`, its residue field.

The two sides of the equation are ideals of `𝒪[K]`:

- `Ideal.relNorm 𝒪[K]` (`Mathlib/RingTheory/Ideal/Norm/RelNorm.lean`, line 270)
  is the relative ideal norm of the finite, torsion-free extension of Dedekind
  domains `𝒪[K] → 𝒪[L]`. It is applied to `𝓂[L]`.
- The right side is `𝓂[K]` raised to `Module.finrank 𝓀[K] 𝓀[L]`, the residue
  degree `f(L / K)`.

So the proposition asserts `N_{𝒪[L]/𝒪[K]}(𝓂[L]) = 𝓂[K] ^ f(L / K)`.

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
- the docstring at lines 389–391;
- the theorem's statement at lines 392–403 and its proof at lines 403–410.

The file opens `namespace LocalClassFieldTheory` (line 23) and
`noncomputable section` (line 29), declares `universe u v w` (line 31) and opens
`scoped ValuativeRel` (line 33). The theorem lies outside every `section` of the
file, and no `variable` is in scope at this point, so its binders are the whole
telescope. `IsNonarchimedeanLocalField` is Mathlib's class: NYLL declares no
class of that name. The source statement is:

```lean
theorem relNorm_maximalIdeal_eq_pow_residue_finrank
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    Ideal.relNorm 𝒪[K] (𝓂[L] : Ideal 𝒪[L]) =
      (𝓂[K] : Ideal 𝒪[K]) ^ Module.finrank 𝓀[K] 𝓀[L] := by
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
| `LocalClassFieldTheory.relNorm_maximalIdeal_eq_pow_residue_finrank` (M162.016) | `Langlands.NYLL.LocalClassFieldTheory.relNorm_maximalIdeal_eq_pow_residue_finrankStatement` |

Row M162.016 of the published partition
[`notes/reuse/nyll-public-port/m145-m168.md`](../../../../../../../notes/reuse/nyll-public-port/m145-m168.md)
reserves `Langlands.NYLL.LocalClassFieldTheory.relNorm_maximalIdeal_eq_pow_residue_finrank`
for the later proof. Section 3 of
[`notes/reuse/nyll-public-port-plan.md`](../../../../../../../notes/reuse/nyll-public-port-plan.md)
gives the `Statement` suffix for the target. The partition's predecessor
`M162.015.END` is scheduling order only: the statement mentions no earlier
source declaration. No NYLL erratum for this module was found in the current
Library's `notes/`.

## Imports and modification record

The direct imports are:

- the source's two Mathlib imports, `Mathlib.FieldTheory.SeparableClosure` and
  `Mathlib.RingTheory.Ideal.Norm.RelNorm`. They supply `Ideal.relNorm`,
  `Algebra.IsSeparable`, `Module.finrank` and `FractionRing.liftAlgebra`;
- `Mathlib.RingTheory.Valuation.Extension`, for `Valuation.HasExtension` and
  the algebra structure `𝒪[K] → 𝒪[L]` with its local-homomorphism instance;
- `Mathlib.NumberTheory.LocalField.Basic`, for the class
  `IsNonarchimedeanLocalField`, the discrete-valuation-ring structure of `𝒪[K]`
  and, through its import of `Mathlib.Topology.Algebra.Valued.ValuativeRel`, the
  scoped notation `𝒪[·]`, `𝓂[·]`, `𝓀[·]`.

In the source these Mathlib declarations arrive through the four NYLL imports,
which are not otherwise needed by this statement and are dropped. Every
transitive import lies in the approved Mathlib environment.

The adaptation makes these changes:

- it moves the theorem's telescope and conclusion into the Prop-valued
  definition above. Binder order, binder kinds, binder names, universes, the
  (here unused) local instance attribute and the conclusion are unchanged;
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
`Langlands.NYLL.LocalClassFieldTheory.relNorm_maximalIdeal_eq_pow_residue_finrank`
and its proof need a separate proof task once this target is in the Library.
The source proof (lines 403–410) obtains separability of
`Frac 𝒪[L] / Frac 𝒪[K]` from M162.015, applies M162.012 to the maximal ideals
`𝓂[L]` over `𝓂[K]`, and rewrites the inertia degree with Mathlib's
`Ideal.inertiaDeg_eq_of_isMaximal`. A proof may follow that route or another.

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
