# Residue-field equivalence from an integral-closure restriction

The single definition
`Langlands.NYLL.LocalFieldTheory.galoisGroupResidueFieldEquivOfIsIntegralClosure`
adapts NYLL unit M160.001. It applies Mathlib's canonical
`IsLocalRing.ResidueField.mapEquiv` to the published actual integer-ring
restriction
`Langlands.NYLL.LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure`.
This is direct data from an existing ring equivalence; it requires no new
preservation or existence theorem.

## Interface and meaning

The complete interface is:

```lean
(K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
[Algebra K L]
[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
[IsIntegralClosure 𝒪[L] 𝒪[K] L]
(σ : Gal(L/K)) : 𝓀[L] ≃+* 𝓀[L]
```

The universe `u` is arbitrary and shared by `K` and `L`. The notation
`Gal(L/K)` denotes the `K`-algebra automorphisms of `L`, without assuming
`IsGalois K L`. The scoped integer ring `𝒪[F]` is the actual subtype
`Valuation.integer (ValuativeRel.valuation F)`. The scoped residue field
`𝓀[L]` is `IsLocalRing.ResidueField 𝒪[L]`, the quotient of that integer
ring by its maximal ideal.

The algebra structure `Algebra K L` and both valuative relations are the
supplied structures. `Valuation.HasExtension` supplies the canonical
integer-ring algebra induced by `algebraMap K L`; `IsIntegralClosure`
refers to that algebra and the canonical inclusion of `𝒪[L]` into `L`.
There is no replacement valuation, scalar structure, or residue quotient.
The interface adds no algebraicity, finite-dimensionality, Galoisness,
topology, completeness, local-field, discrete-valuation, finite-residue,
prime, or preservation-certificate hypothesis.

## Construction and scope

The complete body is:

```lean
IsLocalRing.ResidueField.mapEquiv
  (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)
```

Write `e` for the integer-ring equivalence in this body. Mathlib's
`mapEquiv e` has forward map `ResidueField.map e.toRingHom` and inverse
map `ResidueField.map e.symm.toRingHom`; its inverse and ring laws are
already provided by Mathlib. Ring equivalences are local homomorphisms
here, so no extra preservation certificate is supplied.

On a residue class represented by `x : 𝒪[L]`, the forward map is the
class represented by `e x`. The published integer-ring construction uses
`galRestrict'` and `AlgEquiv.ofAlgHom`, rather than the original explicit
subtype constructors. Its agreement in the field with `σ (x : L)` is
propositional via Mathlib's `algebraMap_galRestrict'_apply`; this module
does not assume the original integer-ring evaluation proofs by `rfl`.
The residue construction itself remains the direct `mapEquiv` application.
See the published [integer-ring companion](../GaloisIntegerRing/Definitions.md)
for that implementation and its source correspondence.

The two explicit imports are
`Mathlib.RingTheory.LocalRing.ResidueField.Basic` and
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.Definitions`.
The original NYLL `GaloisIntegerRing` and `ResidueGalois` import closure is
not imported. The unused original namespace opening
`_root_.LocalFieldTheory.IsNonarchimedeanLocalField` is omitted.

Author checks through `lean_check` succeeded with these two imports in the
approved Lean 4.34.0 / Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` environment, without warnings.
Complete unapplied signature and body inspection confirmed the single
arbitrary universe, exact hypotheses, canonical residue codomain, and
direct body. Private whole-function and residue-reduction checks also
compiled. These are author diagnostics, separate from independent review.

Only M160.001 is extracted. This file exports no standalone evaluation
theorem, base-residue algebra equivalence, automorphism-group homomorphism,
action instance, or inertia kernel. In particular, M160.002 and
M160.005–006 remain separate units. There is no host inertia or
reciprocity comparison in this construction.

## Source correspondence and attribution

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueGalois.lean`, lines 35–41](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueGalois.lean#L35-L41),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. Its file SHA-256 is
`b3c47318364659eb1a14b872f8462a2284f47125b1d84391c5c93a3ba87f2c67`.
The original-to-adapted name is
`LocalFieldTheory.galoisGroupResidueFieldEquivOfIsIntegralClosure` to
`Langlands.NYLL.LocalFieldTheory.galoisGroupResidueFieldEquivOfIsIntegralClosure`.
The [public partition](../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m160)
identifies this declaration as M160.001.

Worker 601 read original `ResidueGalois.lean` lines 1–54, including its
namespace, universe, complete definition, and following reduction formula.
Original `GaloisIntegerRing.lean` lines 1–91 were also read, including the
construction at 52–65 and evaluation formulas at 70–91. That source file
has SHA-256
`5f84d148f49ea9a28bdcbd07b7d16e902ab47b6f47f37a88347848801bbb14b3`.
Mathlib's `RingTheory/LocalRing/ResidueField/Basic.lean` lines 1–185
were read in the approved environment, including `map`, `map_residue`,
and `mapEquiv`.

The readable original belongs to registration
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable errata file was present under the project's or current
Library's `notes/errata` locations. The public partition records no
patch10 change to either source module.

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex). The original Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are already retained in
the Library and are unchanged. Both were compared byte for byte with the
pinned source. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The NOTICE has no source-specific entry for `ResidueGalois.lean`.

Worker 601 isolated this definition, prefixed its namespace, reduced its
imports, omitted the unused namespace opening, and wrote this companion
on 26 October 2026. No adapted draft or patch10 code was reused.
The integer-ring definition and Mathlib are reused by import and Lean
name; their implementations are not copied into this unit.
