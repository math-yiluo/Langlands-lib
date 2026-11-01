# Canonical integer rings in finite separable local extensions: proof

The theorem
`Langlands.NYLL.LocalFieldTheory.localCompleteDVF_integerRing_properties.{u,v}`
proves exactly the published closed proposition
`Langlands.NYLL.LocalFieldTheory.LocalCompleteDVFIntegerRingPropertiesStatement.{u,v}`.
Its unapplied type is that named proposition. Its only declaration
parameters are the independent universe levels `u` and `v`.

The proposition internally quantifies `K : Type u`, `L : Type v`, their
supplied field structures, the supplied `Algebra K L`, finite
dimensionality and separability, and independently supplied
`ValuativeRel`, `TopologicalSpace` and `IsNonarchimedeanLocalField` instances
on each field. Its final premise is exactly
`Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)`
along that algebra. There is no additional premise. In particular,
integrality and module finiteness are conclusions, and the identity
extension is included.

Write
`vK := ValuativeRel.valuation K`,
`vL := ValuativeRel.valuation L`,
`OK := vK.valuationSubring` and `OL := vL.valuationSubring`.
The conclusion is precisely

```lean
IsIntegralClosure OL OK L ∧ Module.Finite OK OL
```

## Actual maps and canonical packages

The rings are the actual valuation subrings inside the supplied fields.
Their elements are the field elements satisfying `vK a ≤ 1` and `vL b ≤ 1`.
The raw extension premise restricts the supplied field map to a map
`OK → OL`: for `a : OK`,

```lean
((algebraMap OK OL a : OL) : L) = algebraMap K L (a : K)
```

The extension equivalence
`Valuation.HasExtension.val_map_le_one_iff` proves that this image belongs
to `OL`. Mathlib's `HasExtension` algebra instances implement exactly this
restriction. Its module action therefore satisfies

```lean
((a • b : OL) : L) = algebraMap K L (a : K) * (b : L)
```

The map `OL → L` is the subtype inclusion; `OK → L` is the subtype
inclusion into `K` followed by the supplied `algebraMap K L`. The
`HasExtension` instances supply both compatible scalar towers. The first
conjunct asserts integral closure along these maps. The second uses the
displayed action.

The published `localCompleteDVF K` and `localCompleteDVF L` package the
same canonical valuations. Their valuation subrings and the corresponding
maps are definitionally the displayed actual rings and maps. The proof
locally installs
`localCompleteDVFValuation_hasExtension K L`, the published M248.002
compatibility result. A `change` to the canonical-package notation is
accepted by definitional equality, including the induced algebra
structures. Extension witnesses are proofs of a proposition; choosing a
local proof of the canonical extension does not change the restricted map.

## Implemented proof

1. Apply the published full-universe theorem
   `Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_completeDVF_extension.{u,u,v}`
   to `K`, `L` and `localCompleteDVF K`. It supplies one
   `target : CompleteDVF.{v,0} L`, an extension witness `hExt`, and
   `IsIntegralClosure target.valuation.valuationSubring OK L`.
   Install the latter two proofs locally and write
   `B := target.valuation.valuationSubring`. The field remains the supplied
   `L : Type v`; only this auxiliary witness's value group is in `Type 0`.
   No field-universe specialization is made.
2. Prove `B ≤ OL`. For `z ∈ B`, the auxiliary integral-closure instance
   gives `IsIntegral OK z` by taking the actual subtype element of `B`
   that maps to `z`. Extend scalars from `OK` to `OL` with
   `IsIntegral.tower_top`. Mathlib's
   `Valuation.Integers.mem_of_integral`, applied to the integers of `vL`,
   now gives `z ∈ OL`: a valuation ring is integrally closed in its field.
3. Prove `OL ≠ ⊤`. The canonical base valuation is nontrivial, so take
   `a : K` with `1 < vK a`. If `OL = ⊤`, its image
   `algebraMap K L a` would have upstairs valuation at most one.
   `HasExtension.val_map_le_one_iff` would imply `vK a ≤ 1`, a contradiction.
   This uses the supplied field map, including when it is the identity.
4. The rank-one discrete valuation in `target` makes `B` a discrete
   valuation ring, hence a ring of Krull dimension at most one. Mathlib's
   `ValuationSubring.eq_of_le_of_ne_top` applied to steps 2 and 3 gives
   `hEq : B = OL` as valuation subrings of this same `L`.
5. Build `hActual : IsIntegralClosure OL OK L` directly. The map `OL → L`
   is injective by `Subtype.ext`. If `z : L` is integral over `OK`, the
   auxiliary closure writes it as the image of `a : B`; rewrite membership
   with `hEq` to obtain an element of `OL` with the same image. Conversely,
   an element of `OL` belongs to `B` by `hEq`, and the auxiliary closure
   makes its image integral over `OK`. Thus the new instance uses the
   actual inclusions and supplied algebras; the proof does not transport
   an unspecified algebra structure along a ring isomorphism.
6. Install `hActual` locally. Apply
   `IsIntegralClosure.finite OK K L OL` and return the two conjuncts.
   The base valuation ring is integrally closed and Noetherian, since its
   canonical valuation is rank-one discrete. Its fraction field is `K`.
   The compatible towers, finite dimensionality and separability are
   exactly those required by this Mathlib finiteness theorem.

The comparison is a local part of this proof. The named Type 0 chosen
extension and its uniqueness theorem are not used as a substitute for
the full-universe existence theorem. All published canonical and chosen
constructions and instances are preserved. No generic uniqueness
interface, supplied/chosen comparison theorem, reciprocity or Weil-system
result is asserted here.

## Source correspondence

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The full 206-line file was read for this proof. Its SHA256 is
`f9f4741aa6a1584e125f571e6095b641f13f0983ccbda6225d9324b9fdc1f27c`.

| Original result | Location | Adapted proof |
| --- | --- | --- |
| M248.003 `LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure` | lines 77–96 | `hActual`, the first conjunct |
| M248.004 `LocalFieldTheory.localCompleteDVF_integerRing_moduleFinite` | lines 98–110 | the final `IsIntegralClosure.finite`, the second conjunct |
| M248.002 `LocalFieldTheory.localCompleteDVFValuation_hasExtension` | lines 58–74 | published `Langlands.NYLL.LocalFieldTheory.localCompleteDVFValuation_hasExtension` |

The source M248.003 installs canonical extension compatibility and invokes
the generic
`target_valuationSubring_isIntegralClosure_of_finite_separable`.
This proof retains the canonical compatibility step and replaces that
invocation by steps 1–5. The full-universe existence theorem is already
published support, selected from the existence and integral-closure part
of source M245.018. Its paired Markdown records that source extraction.
The short local overring comparison is adapted from Worker 1199's earlier
published `ChosenUniquenessProof`; here it applies to the newly obtained
full-universe witness and the supplied canonical upstairs ring. The
integral-closure instance is then constructed directly for that ring.
M248.004's Mathlib finiteness step is retained.

The source's `𝒪[K]` and `𝒪[L]` notation denotes the canonical valuation
integer rings. The published target expands these to
`ValuativeRel.valuation` valuation subrings, whose underlying types are
definitionally those integer rings. The proof groups the two results
under the published closed target, introduces its internal binders,
prefixes the namespace with `Langlands.NYLL`, and qualifies Mathlib's
`Valuation.HasExtension` with `_root_`. Focused imports replace the
original import list. No statement or dependency is edited.

## Attribution and environment

The registered original snapshot is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The registered attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The selected source module has no patch10 compatibility edit. No applicable
erratum was present in the project or current Library errata locations
on 1 November 2026.

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi; authors Naganori Yamaguchi (assisted by OpenAI
Codex). The Apache-2.0
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged, with SHA256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively. The root NOTICE has no entry for this selected file.

Worker 1199 implemented this proof and wrote this explanation on
1 November 2026. Worker 106 supplied the exact target specification and
source-routing context; the frozen published statement is credited to
Workers 384 and 106 in its own pair. The imported full-universe existence
proof and canonical compatibility proof retain Worker 785's adaptation
credits. No implementation draft from another worker was reused in this
proof.

The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0 / Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Upstream used Lean 4.35.0-rc2 / Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
