# The whole Galois group as decomposition group: coercion

This module proves one theorem in `Langlands.NYLL.LocalClassFieldTheory`,
the proof phase of source row M244.002:

```lean
theorem toDecompositionGroupOfEqTop_coe :
    toDecompositionGroupOfEqTop_coeStatement.{u, v}
```

Its type is exactly the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.toDecompositionGroupOfEqTop_coeStatement`
(module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueActionIndex.U002.Statements`),
at the universe parameters `u` and `v` of that definition. That
proposition says: for a field `K : Type u`, a field `L : Type v` with
`Algebra K L`, a valuation ring `A` of `L` with
`hA : decompositionGroup K A = ⊤`, and `sigma : L ≃ₐ[K] L`, the coercion
back to `L ≃ₐ[K] L` of `toDecompositionGroupOfEqTop K A hA sigma` is
`sigma`. There is no Galois hypothesis. Read the statement's Markdown for
the meaning of each binder.

## The proof

```lean
  intro K L _ _ _ A hA sigma
  rfl
```

The proof introduces the eight binders of the closed proposition: `K`,
`L`, the three instance arguments `Field K`, `Field L` and `Algebra K L`,
then `A`, `hA` and `sigma`. The goal is

```lean
(toDecompositionGroupOfEqTop K A hA sigma : L ≃ₐ[K] L) = sigma
```

The published definition `toDecompositionGroupOfEqTop` (source row
M244.001) is a `MonoidHom` structure whose function sends `sigma` to the
subgroup element `⟨sigma, _⟩`. Applying the homomorphism and taking the
underlying element of the subgroup reduces to `sigma` by unfolding
definitions, so `rfl` closes the goal. This is the source proof.

The proof uses no lemma. Its only dependencies are the published statement
module, which imports the M244.001 definition and the M239.001
abbreviation `decompositionGroup`, and Mathlib. Development checks of
this exact Lean file in environment `5c94c648` (by Worker 85 and again by
Worker 371) reported no errors and no warnings. The axioms of the theorem
are the standard `propext`, `Classical.choice` and `Quot.sound`. The proof
term adds none: they enter through the Mathlib and Library declarations
that the statement mentions.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean>).
The complete file was read and its SHA-256 verified as
`985bdcfc1cc21860cc65bbb96dc92b1a0ec09dc05eadd6d4f46b4b0a551f4581`.
The `omit [IsGalois K L] in` line is line 52, the docstring line 53, the
signature lines 54–58, and the proof `rfl` line 59.

| Source unit and original declaration | Adapted declaration |
| --- | --- |
| M244.002, `LocalClassFieldTheory.toDecompositionGroupOfEqTop_coe` | `Langlands.NYLL.LocalClassFieldTheory.toDecompositionGroupOfEqTop_coe`, proving `toDecompositionGroupOfEqTop_coeStatement` |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 85 made these changes:

- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
- The theorem's type is the published closed proposition instead of the
  source signature with section variables. The proof therefore first
  introduces the binders and then uses the source proof `rfl`.
- The source `@[simp]` attribute is omitted. The theorem's type is a
  proposition definition, which is not in the form of a simp lemma. A
  consumer applies the theorem to its arguments instead.
- The source imports are replaced by the published U002 Statements module.
  All other declarations of the source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. It also records these modifications. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only the M244.002 proof. The other rows of the source
file are not part of this unit.
