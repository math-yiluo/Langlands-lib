# Integrality of the valuation integer ring over the base

This module adapts two NYLL declarations: the Prop-valued class
`Langlands.NYLL.LocalFieldTheory.ValuativeExtension` and its canonical instance
`Langlands.NYLL.LocalFieldTheory.valuativeExtensionOfIsIntegralClosure`.

## The class

The complete telescope of the class is

```lean
class ValuativeExtension (K : Type u) (L : Type v) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L] : Prop where
  integer_isIntegral : ∀ x : 𝒪[L], IsIntegral 𝒪[K] (x : L)
```

The universes `u` and `v` are independent. `𝒪[K]` is Mathlib's scoped
`ValuativeRel` notation for `Valuation.integer (ValuativeRel.valuation K)`: the
subring of elements of `K` whose valuation is at most one. The relation
`ValuativeRel K` is supplied data and need not come from a local field.

The class has exactly one field. It says that every element `x` of the
valuation integer ring `𝒪[L]`, viewed in `L`, is a root of a monic polynomial
with coefficients in `𝒪[K]`. The `𝒪[K]`-algebra structure on `L` is Mathlib's
`Algebra.ofSubsemiring`, which restricts `Algebra K L` to the subring
`𝒪[K]`; the inclusion `𝒪[L] → L` is the subtype coercion. The class asserts
nothing else. In particular, it does not say that integral elements of `L` lie
in `𝒪[L]`, that the valuation on `L` restricts to the one on `K`, or that `L`
is finite over `K`. Under it, the integral closure of `𝒪[K]` in `L` contains
`𝒪[L]`; the reverse inclusion is not part of the class.

## The canonical instance

```lean
instance valuativeExtensionOfIsIntegralClosure
    (K : Type u) (L : Type v) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    ValuativeExtension K L
```

`K` and `L` are explicit, as in the source. The hypothesis
`IsIntegralClosure 𝒪[L] 𝒪[K] L` says that `𝒪[L] → L` is injective and that its
image is exactly the set of elements of `L` integral over `𝒪[K]`. Its algebra
structures are `Algebra.ofSubsemiring` for `𝒪[K] → L` and Mathlib's
`Valuation.instAlgebraSubtypeMemSubringInteger` for `𝒪[L] → L`. No algebra
structure `𝒪[K] → 𝒪[L]` and no `Valuation.HasExtension` instance is used.

The proof uses Mathlib's `IsIntegralClosure.isIntegral_iff`, an element of `L`
is integral over `𝒪[K]` exactly when it lies in the image of `𝒪[L]`, and
applies its reverse direction to the witness `⟨x, rfl⟩`. Only that inclusion
is needed, so the instance keeps only the integrality half of the integral
closure hypothesis.

The source docstring, retained in the Lean file, says that the hypothesis
"makes the target valuation an extension of the base valuation". The
declaration proves only the integrality statement above. It proves no
comparison of the two valuations.

## Source and correspondence

These are units M127.002 and M127.003 of the
[NYLL declaration partition](../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m127).
The exact original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuativeExtension.lean`,
SHA-256 `97302922464ef8900f59a8cbc8723fe111c4033eb1d5a63cdbea867ecd10bb56`.
Lines 53–59 open `namespace LocalFieldTheory`, the `noncomputable section`,
`universe u v` and `open scoped ValuativeRel`. Lines 61–68 state the class, and
lines 70–77 the instance; lines 79–80 close the section and namespace. The
complete original file was read for this extraction.

The source is retained under the registered snapshot
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, in its
`n-yamaguchi-0729--ClassFieldTheory/source/` directory. The attribution
supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL erratum was found in the project's published errata. The port plan
records no patch10 change to this source module.

| Unit | Original name | Adapted name |
| --- | --- | --- |
| M127.002 | `LocalFieldTheory.ValuativeExtension` (class, line 64) | `Langlands.NYLL.LocalFieldTheory.ValuativeExtension` |
| M127.002 | `LocalFieldTheory.ValuativeExtension.integer_isIntegral` (field, line 68) | `Langlands.NYLL.LocalFieldTheory.ValuativeExtension.integer_isIntegral` |
| M127.003 | `LocalFieldTheory.valuativeExtensionOfIsIntegralClosure` (instance, line 72) | `Langlands.NYLL.LocalFieldTheory.valuativeExtensionOfIsIntegralClosure` |

The parameter order, instance arguments, universes, field type, declaration
docstrings and instance proof are unchanged. Only the namespace has the `Langlands.NYLL`
prefix.

## Not Mathlib's `ValuativeExtension`

Mathlib has a different root class `ValuativeExtension A B`, in
`Mathlib/RingTheory/Valuation/ValuativeRel/Basic.lean`. Its single field
`vle_iff_vle` says that the valuative relation on `A` is the one induced from
`B` along `algebraMap A B`. That compares relations; it says nothing about
integrality, and this module states or proves no relation between the two
classes. Inside
`namespace Langlands.NYLL.LocalFieldTheory` the name `ValuativeExtension`
resolves to the namespaced class. A Lean-service check confirmed that the
instance's conclusion is `Langlands.NYLL.LocalFieldTheory.ValuativeExtension K L`.

## Imports, reuse and scope

The imports are the original module's three Mathlib imports:
`Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic`,
`Mathlib.RingTheory.Valuation.Extension` and
`Mathlib.Topology.Algebra.Valued.ValuativeRel`. No NYLL or Library module is
imported.

The source theorem M127.001, `Valuation.IsNontrivial.of_hasExtension`
(lines 17–51), is used by neither declaration. It is omitted and needs its own
statement and proof units. The partition's scheduling edge from M127.001.END to
M127.002 is therefore not a dependency of this unit.

No Mathlib or Library declaration was found that bundles exactly this
integrality condition for valuation integer rings of `ValuativeRel` fields.
Mathlib's `Algebra.IsIntegral 𝒪[K] 𝒪[L]` would need an algebra structure
`𝒪[K] → 𝒪[L]`, which this source does not assume. The class is therefore
ported as stated rather than replaced.

The instance is global, as in the source. It is the only instance of the new
namespaced class, so it cannot conflict with a Mathlib or host instance. It
fires only when an `IsIntegralClosure 𝒪[L] 𝒪[K] L` instance is available, and
it creates no instance of Mathlib's root `ValuativeExtension`, `Algebra` or
`IsIntegralClosure`. Source consumers such as M129
(`NonarchimedeanLocalField/Norm.lean`) take the class as a hypothesis to
restrict field norms to valuation integer rings. This module proves no norm
result.

## Lean check

Lean-service builds in Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` (environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`) finished with no errors or warnings.
They inspected both declarations, which have level parameters `u` and `v` and
use only `propext`, `Classical.choice` and `Quot.sound`. A separate private
check confirmed that `inferInstance` finds the instance from an
`IsIntegralClosure 𝒪[L] 𝒪[K] L` hypothesis and that the field projection has
the stated type.

## Attribution and modifications

The original copyright and author header is retained verbatim: copyright 2026
Naganori Yamaguchi (`https://github.com/n-yamaguchi-0729`), all rights
reserved; authors Naganori Yamaguchi (assisted by OpenAI Codex). The source is
released under Apache-2.0. The unchanged upstream
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are already in the Library;
their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The upstream NOTICE has no source-specific entry for `ValuativeExtension.lean`.

Worker 176 extracted these two source declarations on 10 November 2026, added
the `Langlands.NYLL` namespace prefix, omitted M127.001, and added a
modification comment and one module-docstring paragraph that distinguishes this
class from Mathlib's root class. Worker 176 also wrote this documentation. The
declaration bodies, declaration docstrings and original imports are unchanged. No patch10
code or other worker's draft was reused.
