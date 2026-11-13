# Successive maximal-ideal power quotient data (M132.054–057,059,064)

This module constructs the actual submodule quotient of `𝓂[K]^n` by the
preimage of `𝓂[K]^(n+1)` under its subtype inclusion. It keeps arbitrary
`K : Type u`, `[Field K] [ValuativeRel K]` and all `n : Nat`. No local-field,
topological or positivity hypothesis is added. The ring and ideal powers are
the canonical Mathlib integer ring and its maximal ideal.

Each original name below has prefix `LocalFieldTheory.`; the corresponding
adapted name has prefix `Langlands.NYLL.LocalFieldTheory.` with the same suffix.

| Unit | Source lines | Original and adapted suffix | Kind |
| --- | --- | --- | --- |
| M132.054 | 748–752 | `maximalIdealPowSuccSubmodule` | abbrev |
| M132.055 | 755–757 | `MaximalIdealPowSuccQuot` | def |
| M132.056 | 760–766 | `maximalIdealPowSuccQuotAddCommGroup` | instance |
| M132.057 | 769–775 | `maximalIdealPowSuccQuotModule` | instance |
| M132.059 | 791–798 | `maximalIdealPowSuccQuotMk` | def |
| M132.064 | 852–870 | `maximalIdealPowSuccQuotLift` | def |

The first five telescopes are `(K : Type u) [Field K] [ValuativeRel K] (n : Nat)`.
The lift keeps `{K : Type u} {P : Sort*} [Field K] [ValuativeRel K]`, explicit
`n`, explicit representative-level function `f`, and the explicit premise
`h : ∀ a b, a - b ∈ maximalIdealPowSuccSubmodule K n → f a = f b`, in source order.
Its arbitrary independent `Sort*` codomain is retained, including Prop-valued
functions; it is not restricted to a type or to a linear map.

Every data and intrinsic proof body is unchanged. The abbreviation is the
`Submodule.comap` of the successor ideal under `Submodule.subtype`; the quotient
type is the Mathlib submodule quotient. The named additive-group and module
instances use `change` followed by `infer_instance` to expose the canonical
structures of the new quotient type. They do not replace an existing instance.
The class map is `Submodule.mkQ`. The general lift uses `Quotient.lift`; its
well-definedness proof retains the source `Quotient.sound` equality and
`Submodule.Quotient.eq` conversion before applying `h`.

Modifications are the namespace prefix and the imports, reduced to
`PrincipalUnits.Definitions` (canonical notation/ideal operations) and
`Mathlib.LinearAlgebra.Quotient.Basic`. Source noncomputable section, universe,
notation scope and `open Filter` are retained. Unneeded intervening source
declarations, including the concrete linear equivalence, are omitted.
There are no additional mathematical changes or separate theorem proofs.
The actual Mathlib submodule quotient constructors are reused by name.
No comparison with principal-unit quotients or host reciprocity is asserted.

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean`.
The complete source file SHA-256 is
`6147c6613cd0176ace8787d7c65a3026d23bd5e23dc3282902d5ea66a0977c83`.
Its readable retained copy is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the published errata notes.

The original copyright, Apache-2.0 license and author header are retained.
The Library files `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are unchanged;
their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 211 performed this extraction and namespace adaptation. No patch10 edit
or other worker's implementation draft was used.
