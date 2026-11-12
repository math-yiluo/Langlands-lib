# Base-field units embedded in extension-field units

This module adapts NYLL M129.004 as the data definition
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.mapBaseUnitsToExtensionUnits`.
For a field extension given by an algebra structure `Algebra K L`, it is the
group homomorphism `Kˣ →* Lˣ` sending a unit of `K` to its image under the
algebra map. The namespace is inherited from the source; the definition does
not assume that either field is a local field.

With independent universes `u` and `v`, the complete telescope is:

```lean
def mapBaseUnitsToExtensionUnits
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    Kˣ →* Lˣ
```

Both fields are explicit arguments. The noncomputable definition is exactly

```lean
Units.map (algebraMap K L).toMonoidHom
```

Mathlib's `Units.map f` applies the monoid homomorphism `f` to the value and
the inverse of each unit. Here `f` is the ring homomorphism `algebraMap K L`
viewed as a monoid homomorphism. Consequently the value in `L` of the image of
`x : Kˣ` is definitionally `algebraMap K L (x : K)`. That evaluation identity
is the separate source lemma M129.005 and is not stated here.

The definition assumes no finite dimensionality, separability, Galois
condition, valuation or topology. No property of the homomorphism, such as
injectivity, and no norm identity is asserted: the degree-power norm formulas
M129.006 and M129.007 need their own statement and proof units.

## Source and correspondence

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Norm.lean`.
The complete file was read; its SHA-256 is
`0e9e3d68b6d964addae89ea2185146fdee7c6b60bf23cfff679a20f34e808eb6`.
The definition and its docstring are lines 67–71. Its universe and section
context is at lines 20–30 (namespace `LocalFieldTheory`, `noncomputable
section`, `universe u v`, namespace `IsNonarchimedeanLocalField`, and
implicit section variables `{K : Type u} {L : Type v}`) and lines 63–65
(section `UnitNorm` with `[Field K] [Field L] [Algebra K L]`).

| Unit | Original declaration | Adapted declaration |
| --- | --- | --- |
| M129.004, lines 67–71 | `LocalFieldTheory.IsNonarchimedeanLocalField.mapBaseUnitsToExtensionUnits` | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.mapBaseUnitsToExtensionUnits` |

The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
in its `n-yamaguchi-0729--ClassFieldTheory/source/` directory. The attribution
supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the published errata.

The source definition binds its own explicit `(K : Type u) (L : Type v)` and
instance arguments, which shadow the section variables. The section variables
are therefore not parameters of the original constant, and its full telescope
is the one displayed above. The earlier section `AlgebraNorm` (lines 32–61),
with its `Module.Free K L` and `Module.Finite K L` variables, ends before this
definition; those classes are not parameters either. The adapted declaration
restates the same explicit binders, so the universes, binder visibility and
order, instance arguments, result type and body are unchanged. Only the
`Langlands.NYLL` namespace prefix is added.

## Imports, reuse and scope

The original module imports `Mathlib.LinearAlgebra.Determinant`,
`Mathlib.RingTheory.Norm.Transitivity`, `Mathlib.RingTheory.Valuation.Integral`
and the NYLL modules `NormUnits`, `NonarchimedeanLocalField.ValuativeExtension`
and `NonarchimedeanLocalField.Basic`. The definition uses none of their
declarations: it needs only `Field`, `Algebra`, `algebraMap`,
`RingHom.toMonoidHom` and `Units.map`. Those imports are replaced by
`Mathlib.Algebra.Algebra.Defs` and `Mathlib.Algebra.Field.Defs`. No NYLL
module is imported. The conservative inventory predecessor M129.003, a
determinant lemma, is neither imported nor copied, and no other source
declaration of the module is included.

The Library's `Langlands.Shimura.AlgebraInvolution.scalarUnits`, in
`Langlands/Shimura/Unitary/Similitude.lean`, uses the same
`Units.map (algebraMap R A).toMonoidHom` expression for a commutative ring `R`
and an `R`-algebra `A`. This source specialization retains explicit field
arguments `K` and `L` and the prescribed NYLL name. The same expression also
occurs inline in `Langlands/ClassFieldTheory/Local/CyclicClassAlgebra.lean`.
Those modules are unchanged and are not imported; no instance is introduced.

This definition supplies algebraic data for the later source lemmas
M129.005–M129.007 and M129.024, which compare it with
`Langlands.NYLL.LocalFieldTheory.normUnits`. It constructs no norm map,
Artin map or reciprocity statement.

## Checks

The focused module check in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) succeeded with no errors or
warnings; the inspected constant has universe parameters `u` and `v`.
A private probe reconstructed the original definition in its source
context: the namespaces, universes, opened scopes and section variables of
lines 20–34 and 61–71, including the shadowed `UnitNorm` variables, with the
three `AlgebraNorm` lemmas omitted. It used the original Mathlib imports;
the original NYLL imports were replaced there by the published `normUnits`
module and the published `ValuativeExtension.Definitions` module, which
supplies the `ValuativeRel` scope opened by the source. Definitional equality of the
whole original constant with the adaptation passed, as did checks of the
complete telescope with independent universes and of the literal body.
The source proofs of M129.005 (`rfl`) and of M129.006 and M129.007
(`simp` with `Algebra.norm_algebraMap`) replayed against this definition and
the published `normUnits`, without errors or warnings. These development
checks provide no independent acceptance and publish none of those lemmas.

## Attribution

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi (`https://github.com/n-yamaguchi-0729`), all rights
reserved; authors Naganori Yamaguchi (assisted by OpenAI Codex).
The original Apache-2.0 [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE) are already
published. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The NOTICE has no source-specific entry for this module.

Worker 177 extracted this single definition on 12 November 2026, added the
`Langlands.NYLL` namespace prefix, replaced the original imports as described
above and wrote this documentation. No patch10 code or another worker's draft
was reused.
