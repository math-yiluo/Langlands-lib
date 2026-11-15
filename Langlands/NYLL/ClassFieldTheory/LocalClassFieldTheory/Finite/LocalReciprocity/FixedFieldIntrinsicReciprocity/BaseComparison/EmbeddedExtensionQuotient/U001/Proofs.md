# Embedded extension quotients: membership in the transported extension subgroup

This module proves the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.intrinsicExtensionSubgroup_iff_ambientEmbeddedFieldStatement`
(source row M274.001) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.intrinsicExtensionSubgroup_iff_ambientEmbeddedField`.
The theorem's type is exactly that proposition, with no parameters of its own.

It imports two published Library modules:

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient.U001.Statements`,
  which contains the target statement;
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U008.Proofs`,
  which proves the pointwise formula
  `intrinsicBaseEquivAmbientEmbeddedField_apply_val` (source row M273.008).

Both published Lean/Markdown pairs and everything they import stay unchanged.

## Target

The target quantifies over fields `K F E : Type` with
`[Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]`,
`[FiniteDimensional K F] [Algebra.IsSeparable K F]`,
`[FiniteDimensional F E] [IsGalois F E]` and a `K`-algebra map
`j : E →ₐ[K] SeparableClosure K`. It sets
`i := j.comp (IsScalarTower.toAlgHom K F E)`, makes `SeparableClosure F` an
`F`-algebra through `separableClosure F (AlgebraicClosure F)` and
`SeparableClosure K` an `F`-algebra through `i`. Then, for every
`e : SeparableClosure F ≃ₐ[F] SeparableClosure K` and every
`tau : (intrinsicAbstractBase F).toSubgroup`, it defines
`jI := e.symm.toAlgHom.comp jF` (`jF` is `j` as an `F`-algebra map),
`EI := finiteGaloisAbstractExtensionOfEmbedding F E jI`, the closed subgroups
`H₀` and `J₀` of `Gal(SeparableClosure K / K)` fixing `i(F)` and `j(E)`, and
`hJH : J₀.toSubgroup ≤ H₀.toSubgroup`. It asserts

```lean
tau ∈ extensionSubgroup (intrinsicAbstractBase F) EI.field EI.below ↔
  intrinsicBaseEquivAmbientEmbeddedField K F i e tau ∈
    extensionSubgroup H₀ J₀ hJH
```

The published statement Markdown describes these data in full.

## Implemented proof

The proof introduces `K F E`, the eleven instance arguments and `j`, unfolds
the statement's `let`/`letI` data with `dsimp only`, recreates `i` and the
`F`-algebra structure on `SeparableClosure K` (through `i`), and introduces
`e` and `tau`. It then recreates the local maps `jF` and `jI` exactly as the
statement defines them.

### Pointwise formula (`hval`)

```lean
  have hval :
      ∀ x : SeparableClosure K,
        (intrinsicBaseEquivAmbientEmbeddedField K F i e tau).1.1 x =
          e (tau.1 (e.symm x)) :=
    intrinsicBaseEquivAmbientEmbeddedField_apply_val K F i e tau
```

This applies the published theorem
`Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply_val`
(the proof of `intrinsicBaseEquivAmbientEmbeddedField_apply_valStatement`) to
`K F i e tau`. The instance arguments of that statement and its two local
algebra structures are the ones in force here. So the image of `tau` acts on
`SeparableClosure K` by `x ↦ e (tau (e.symm x))`.

### The equivalence

```lean
  change
    tau.1 ∈ (AlgHom.fieldRange jI).fixingSubgroup ↔
      (intrinsicBaseEquivAmbientEmbeddedField K F i e tau).1 ∈
        (AlgHom.fieldRange j).fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff,
    IntermediateField.mem_fixingSubgroup_iff]
```

Membership in `extensionSubgroup H J h = J.toSubgroup.subgroupOf H.toSubgroup`
is membership of the underlying element in `J.toSubgroup`. The field of
`finiteGaloisAbstractExtensionOfEmbedding F E jI` is the closed subgroup
fixing `jI(E)`, and `closedFixingSubgroup` has underlying subgroup
`fixingSubgroup`. So the goal is definitionally the displayed one, and
Mathlib's `IntermediateField.mem_fixingSubgroup_iff` turns both sides into
pointwise fixing conditions.

- Forward: let `tau` fix `jI(E)` and let `x = j y`. By `hval` the image of
  `tau` sends `j y` to `e (tau (e.symm (j y)))`, which is definitionally
  `e (tau (jI y))`. Since `tau` fixes `jI y`, this is
  `e (jI y) = e (e.symm (j y)) = j y` (`AlgEquiv.apply_symm_apply`).
- Backward: let the image fix `j(E)` and let `x = jI y`. Applying the
  injective map `e`, the goal becomes
  `e (tau (e.symm (j y))) = e (e.symm (j y))`. Rewriting the right side with
  `e.apply_symm_apply` and the left side with `hval` backwards reduces it to
  the hypothesis at `j y`.

The proof uses only Mathlib, the M273.008 theorem and the declarations the
statement module imports.

## Relation to the original proof

The source proof (lines 71–125) has the same steps and rewrites with the same
M273.008 theorem. It differs in two places:

- the source calls `intrinsicBaseEquivAmbientEmbeddedField_apply_val K F i e tau`
  at each rewrite; this proof names that instance `hval` once;
- the source also introduces the local data `EI`, `H₀`, `J₀` and `hJH`
  before the `change` step. After `dsimp only` they are not needed, so this
  proof omits them.

## Original source

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean>),
SHA-256 `6d057d4d7df649ce5d67657b86688b0532b975cbc5d03be5b15582dccdc140da`.
The theorem `LocalClassFieldTheory.intrinsicExtensionSubgroup_iff_ambientEmbeddedField`
has its docstring at lines 28–30, its signature at lines 31–70 and its proof
at lines 71–125. The header occupies lines 1–5.

| Original | Adapted |
| --- | --- |
| Type of `LocalClassFieldTheory.intrinsicExtensionSubgroup_iff_ambientEmbeddedField` | Published `Langlands.NYLL.LocalClassFieldTheory.intrinsicExtensionSubgroup_iff_ambientEmbeddedFieldStatement` (U001 Statements) |
| Proof of the same theorem | `Langlands.NYLL.LocalClassFieldTheory.intrinsicExtensionSubgroup_iff_ambientEmbeddedField` (this module) |
| `LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply_val` (M273.008), used in the proof | Published `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply_val` (`...BaseComparison.IntrinsicBaseEquivalence.U008.Proofs`), named `hval` for this `tau` |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 (14 November 2026) and Worker 437 (15 November 2026) made these
changes:

- the namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`;
- the theorem proves the published closed proposition instead of restating
  its telescope;
- the M273.008 instance is named `hval`;
- the unused local data `EI`, `H₀`, `J₀` and `hJH` are omitted;
- the source imports are replaced by the U001 Statements module and the
  published M273.008 proof module;
- all other declarations of the source file are omitted.

Worker 57's earlier draft derived `hval` inside the proof from the definition
of `intrinsicBaseEquivAmbientEmbeddedField`, because the M273.008 proof was
not yet published. That proof is now in the Library, and this module uses it
as the source does.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0
notice, followed by the dated modification record. The existing
[LICENSE](../../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../../licenses/NYLL/NOTICE) are retained.

This module contains only the M274.001 proof. The M274.002 proof is in the
U002 Proofs module, which imports this one.
