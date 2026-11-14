# Norm classes under compatible field equivalences: proof

This module proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.normClass_mapEquivStatement`
(NYLL source unit M283.007) under the required theorem name
`Langlands.NYLL.LocalClassFieldTheory.normClass_mapEquiv`.

## Statement and scope

The theorem's type is exactly the named closed proposition. Its parameters
are four fields `F E F₀ E₀ : Type`, algebra structures `[Algebra F E]` and
`[Algebra F₀ E₀]`, and ring equivalences `phiF : F ≃+* F₀` and
`phiE : E ≃+* E₀` satisfying

```lean
RingHom.comp (algebraMap F₀ E₀) phiF.toRingHom =
  RingHom.comp phiE.toRingHom (algebraMap F E)
```

For units `a x : Fˣ` with `normClass F E a = normClass F E x`, it concludes

```lean
normClass F₀ E₀ (Units.mapEquiv phiF.toMulEquiv a) =
  normClass F₀ E₀ (Units.mapEquiv phiF.toMulEquiv x)
```

Here `normClass` is `Langlands.NYLL.LocalFieldTheory.normClass`, the actual
quotient map by the range of
`Langlands.NYLL.LocalFieldTheory.normUnits K L = Units.map (Algebra.norm K)`.
All four fields remain in universe zero. There is no finite-dimensionality,
separability, Galois, valuation or topology premise.

## Actual imports

The module imports three published Library modules:

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U006.Statements`,
  which defines the exact target.
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U006.Proofs`,
  which proves the sibling theorem
  `Langlands.NYLL.LocalClassFieldTheory.normUnits_mapEquiv` (M283.006).
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U031.Proofs`,
  which proves
  `Langlands.NYLL.LocalFieldTheory.normClass_eq_iff_exists_norm_div`.

The target's Lean/Markdown pair and all its imports are unchanged.

## Implemented proof

After introducing the parameters, the proof follows the original tactic
proof:

1. Rewrite both the hypothesis and goal using
   `normClass_eq_iff_exists_norm_div`. Equality of the original classes
   supplies `y : Eˣ` with `a / x = normUnits F E y`; the goal asks for a
   corresponding unit norm in `E₀`.
2. Choose `Units.mapEquiv phiE.toMulEquiv y` as the witness.
3. Apply the published `normUnits_mapEquiv` to the compatible equivalences
   and `y`. This identifies the norm of the witness with the transport by
   `phiF` of `normUnits F E y`.
4. Rewrite the quotient of the transported units using `← map_div`, then
   use the witness equation. The symmetric form of step 3 closes the goal.

The norm-class characterization is universe polymorphic and is instantiated
at universe zero here. The sibling theorem applies without adding a
finite-dimensionality premise.

The development Lake build and declaration inspection succeeded without
errors or warnings. Inspection reports no universe parameters and only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Original correspondence and adaptation

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean>).
Its SHA-256 is
`b430f3810416cb42cc7c61df63be3691b219a5fe39c0bc7c0c2a74292298bfa0`.
The original theorem is `LocalClassFieldTheory.normClass_mapEquiv`:
docstring line 211, signature lines 212–224, proof lines 225–231.
The sibling `normUnits_mapEquiv` appears in lines 187–209.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original header, relevant source declarations and source hash were
checked against the retained snapshot; the public errata directory has no
matching NYLL or source-collection erratum.

Worker 56 prepared the task's shared draft on 13 November 2026, inlining the
sibling proof to avoid depending on its then-separate proof task. Worker 520
adapted that draft on 14 November 2026 to import and use the now-published
sibling theorem. The final tactic proof after the initial `intro` matches
the original proof.

The adaptation prefixes the original namespace with `Langlands.NYLL` and
proves the closed published proposition, so it introduces the original
binders inside the proof. It opens `Langlands.NYLL.LocalFieldTheory` for
the same names that the source resolves through `open LocalFieldTheory`.
The three focused imports replace the original imports
`Mathlib.FieldTheory.Galois.Basic` and
`Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.EmbeddedFrobeniusTransport`.
The original `noncomputable section`, other namespace openings and other
declarations are omitted. No instance or simp attribute is installed.

## Attribution

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 notice and authorship line including OpenAI Codex assistance.
The dated modification record identifies Worker 56 and Worker 520.
The existing [LICENSE](../../../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) retain hashes
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively.
