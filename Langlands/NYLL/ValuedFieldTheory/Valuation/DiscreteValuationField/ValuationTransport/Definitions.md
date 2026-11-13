# NYLL M106-valuation-ring-transport: data

The actual ring equivalence from the valuation ring of a comapped valuation to the original valuation ring. It acts by the supplied field equivalence on ambient elements and by its inverse in the opposite direction. The fields occupy independent arbitrary universes `u` and `w`; the ordered value group occupies `v`. No discreteness assumption is imposed.

## Exact source correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ValuationTransport.lean`.
The original file SHA-256 is `173bac49cc97f73e78074fce0bd629dc212ad06dd0ead5f0348e76be9a045890`.
The readable original is retained under registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, at
`n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ValuationTransport.lean`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Original name | Source declaration lines | Adapted name |
| --- | --- | --- | --- |
| M106.003 | `ValuationTheory.DiscreteValuationField.Valuation.valuationSubringRingEquivOfComap` | 99–110 | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.valuationSubringRingEquivOfComap` |

## Complete data and context

The Lean module retains the following complete context and data. Only the
namespace prefix changes in this display.

```lean
universe u v w

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable {Γ : Type v} [LinearOrderedCommGroupWithZero Γ]

noncomputable def valuationSubringRingEquivOfComap
    (v : _root_.Valuation K Γ) (e : L ≃+* K) :
    (v.comap (e : L →+* K)).valuationSubring ≃+* v.valuationSubring where
  toFun x := ⟨e (x : L), x.2⟩
  invFun y := ⟨e.symm (y : K), by
    change v (e (e.symm (y : K))) ≤ 1
    rw [e.apply_symm_apply]
    exact y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply (x : L))
  right_inv y := Subtype.ext (e.apply_symm_apply (y : K))
  map_mul' x y := Subtype.ext (map_mul e (x : L) (y : L))
  map_add' x y := Subtype.ext (map_add e (x : L) (y : L))
```

## Adaptation and reuse

Worker 202 prefixed the source namespace with `Langlands.NYLL`, retained the
original declaration names, and reduced the import closure to:

- `Mathlib.RingTheory.Valuation.ValuationSubring`

The source's complete variable context (lines 27–28), noncomputable modifier, result type, six structure fields and all proof terms are retained verbatim. The source import of the chosen-DVF module is unnecessary for this construction. The implementation uses Mathlib's actual valuation subrings and ring equivalences.

The Library and Mathlib were searched for these exact data declarations before
authoring. Related canonical Mathlib structures are reused directly through the
listed imports. This module introduces no global instance and copies no other
worker's draft.

## Attribution and scope

The original copyright and author header is retained verbatim. The Apache-2.0
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain in the Library, with
SHA-256 values `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The public partition reports no patch10 modification for this module.
This supporting data asserts no host reciprocity, Tate, cup-product, transfer
or class-formation result.
