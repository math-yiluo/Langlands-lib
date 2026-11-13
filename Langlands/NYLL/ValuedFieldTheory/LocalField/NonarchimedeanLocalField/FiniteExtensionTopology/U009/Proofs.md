# The spectral valuation on a finite extension extends the base valuation

This module proves the published closed proposition
`Langlands.NYLL.LocalFieldTheory.finiteExtensionSpectralValuation_hasExtensionStatement`
(source row M270.009) by the theorem
`Langlands.NYLL.LocalFieldTheory.finiteExtensionSpectralValuation_hasExtension`.
The theorem's type is exactly that proposition, with no parameters of its own.

Its only import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology.U009.Statements`.
That published Lean/Markdown pair and everything it imports stay unchanged.

## Target

Unfolded, the target is

```lean
∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    letI : NontriviallyNormedField L :=
      Langlands.LocalField.FiniteExtension.normedField K L
    letI : ValuativeRel L := Langlands.LocalField.FiniteExtension.valuativeRel K L
    Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)
```

So for a finite extension `L` of a nonarchimedean local field `K`, with `L`
given the Library's spectral valuative relation, the canonical valuation of
`L` restricts along `algebraMap K L` to a valuation equivalent to the
canonical valuation of `K`. Mathlib's class `Valuation.HasExtension vK vL`
has the single field
`val_isEquiv_comap : vK.IsEquiv (vL.comap (algebraMap K L))`, that is,
`vK x ≤ vK y ↔ vL (algebraMap K L x) ≤ vL (algebraMap K L y)` for all
`x y : K`.

## Implemented proof

```lean
  intro K L _ _ _ _ _ _ _
  let : ValuativeRel L := Langlands.LocalField.FiniteExtension.valuativeRel K L
  refine ⟨fun x y => ?_⟩
  change ValuativeRel.valuation K x ≤ ValuativeRel.valuation K y ↔
    ValuativeRel.valuation L (algebraMap K L x) ≤ ValuativeRel.valuation L (algebraMap K L y)
  rw [← Valuation.Compatible.vle_iff_le, ← Valuation.Compatible.vle_iff_le]
  exact (Langlands.LocalField.FiniteExtension.algebraMap_vle_iff K L x y).symm
```

1. The nine introductions are the two fields and their seven instance
   arguments. The two `letI` instances of the statement are inlined into the
   goal, so they are not introduced.
2. The `let` makes the Library relation `valuativeRel K L` a local instance
   again, so that the canonical valuation of `L` and the relation `≤ᵥ` on `L`
   below refer to it.
3. `refine ⟨fun x y => ?_⟩` supplies the single field `val_isEquiv_comap`.
   `Valuation.IsEquiv` is a pointwise iff, so one goal remains for each pair
   `x y : K`. The `change` writes it with `Valuation.comap_apply` unfolded.
4. `Valuation.Compatible.vle_iff_le`, the field of Mathlib's class
   `Valuation.Compatible` (in
   `Mathlib/RingTheory/Valuation/ValuativeRel/Basic.lean`), says
   `x ≤ᵥ y ↔ v x ≤ v y` for a valuation `v` compatible with the relation.
   The canonical valuation `ValuativeRel.valuation` of a relation is
   compatible with it by a Mathlib instance in the same file. Rewriting backwards twice turns
   both sides into relation comparisons:
   `x ≤ᵥ y ↔ algebraMap K L x ≤ᵥ algebraMap K L y`.
5. The published Library theorem
   `Langlands.LocalField.FiniteExtension.algebraMap_vle_iff K L x y`
   (`Langlands/LocalField/FiniteExtension.lean`, line 52) states
   `algebraMap K L x ≤ᵥ algebraMap K L y ↔ x ≤ᵥ y` for the relation
   `valuativeRel K L`. Its symmetric form closes the goal.

No hypothesis, instance or auxiliary declaration is added. The normed-field
instance of the statement is not used by the proof.

## Relation to the original proof

The original source proves the theorem differently (source lines 189–218):
it installs a rank-one structure on the valued base field, applies
`Valuation.HasExtension.ofComapInteger` and compares the valuation integers
through `spectralNorm_extends` and `Valued.toNormedField.norm_le_one_iff`.
The published statement replaced the source's own spectral norm and
relation (M270.003, M270.007) by the Library's
`Langlands.LocalField.FiniteExtension.normedField` and
`Langlands.LocalField.FiniteExtension.valuativeRel`. For these, the Library
already proves the order comparison `algebraMap_vle_iff` (itself by
`spectralNorm_extends`), so the shorter route above is used.

## Original source

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionTopology.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionTopology.lean>),
SHA-256 `62f5ffd2e815d3b14c80abb812cfc839d329043a43e8da5c9f29cd655d222b8f`.
The theorem `LocalFieldTheory.finiteExtensionSpectralValuation_hasExtension`
has its docstring at lines 178–179, its signature at lines 180–188 and its
proof at lines 189–218. The header occupies lines 1–5.

| Original | Adapted |
| --- | --- |
| Type of `LocalFieldTheory.finiteExtensionSpectralValuation_hasExtension` | Published `Langlands.NYLL.LocalFieldTheory.finiteExtensionSpectralValuation_hasExtensionStatement` (U009 Statements) |
| Proof of the same theorem | `Langlands.NYLL.LocalFieldTheory.finiteExtensionSpectralValuation_hasExtension` (this module), by a different route |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes: the namespace `LocalFieldTheory` is prefixed
with `Langlands.NYLL`; the theorem proves the published closed proposition
instead of restating its telescope; the proof is replaced as described
above; the source imports are replaced by the single U009 Statements
import; all other declarations of the source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0
notice, followed by the dated modification record. The existing
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained.

This module contains only the M270.009 proof.
