# Embedded extension quotients: image of the intrinsic extension subgroup

This module proves the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.map_intrinsicExtensionSubgroup_eq_ambientEmbeddedFieldStatement`
(source row M274.002) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField`.
The theorem's type is exactly that proposition, with no parameters of its own.

Its only import is the published U001 Proofs module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient.U001.Proofs`,
which proves M274.001 and imports the published U001 Statements module
containing this target (and the published M273.008 proof module it uses).
The statement's Lean/Markdown pair, the U001 Proofs pair and everything they
import stay unchanged.

## Target

With the same parameters and local data as M274.001 (fields `K F E : Type`
in a tower with `F / K` finite separable and `E / F` finite Galois,
`j : E →ₐ[K] SeparableClosure K`, its restriction `i` to `F`, the
`F`-algebra structures through `separableClosure F (AlgebraicClosure F)` and
`i`, an `F`-algebra isomorphism `e : SeparableClosure F ≃ₐ[F] SeparableClosure K`,
`jI`, `EI`, `H₀`, `J₀` and `hJH`), and with
`psi := intrinsicBaseEquivAmbientEmbeddedField K F i e`, the target asserts

```lean
(extensionSubgroup (intrinsicAbstractBase F) EI.field EI.below).map
    psi.toMonoidHom =
  extensionSubgroup H₀ J₀ hJH
```

## Implemented proof

```lean
  intro K F E _ _ _ _ _ _ _ _ _ _ _ j
  dsimp only
  let i := j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) := i.toRingHom.toAlgebra
  intro e
  let psi := intrinsicBaseEquivAmbientEmbeddedField K F i e
  have hmem := intrinsicExtensionSubgroup_iff_ambientEmbeddedField K F E j e
  ext sigma
  constructor
  · rintro ⟨tau, htau, rfl⟩
    exact (hmem tau).1 htau
  · intro hsigma
    let tau : (intrinsicAbstractBase F).toSubgroup := psi.symm sigma
    refine ⟨tau, ?_, psi.apply_symm_apply sigma⟩
    apply (hmem tau).2
    have htauImage : psi tau = sigma := psi.apply_symm_apply sigma
    rw [htauImage]
    exact hsigma
```

After unfolding the statement's local data and introducing `e`, the proof
specializes the M274.001 theorem
`intrinsicExtensionSubgroup_iff_ambientEmbeddedField` (U001 Proofs) to
`K F E j e`, giving `hmem : ∀ tau, tau ∈ (intrinsic extension subgroup) ↔
psi tau ∈ (ambient extension subgroup)`. It proves equality of subgroups
elementwise (`ext sigma`):

- an element of the image has the form `psi tau` with `tau` in the intrinsic
  extension subgroup, so it lies in the ambient one by `hmem`;
- conversely, for `sigma` in the ambient extension subgroup, the preimage
  `tau := psi.symm sigma` satisfies `psi tau = sigma`
  (`MulEquiv.apply_symm_apply`), so `tau` lies in the intrinsic extension
  subgroup by `hmem`, and `sigma` is its image.

The proof uses only Mathlib, the M274.001 theorem and the declarations the
statement module imports.

## Relation to the original proof

The source proof (lines 170–217) has the same steps. It differs in two
places:

- the source calls `intrinsicExtensionSubgroup_iff_ambientEmbeddedField K F E j e tau`
  at each use; this proof names the specialization `hmem` once;
- the source also introduces the local data `jF`, `jI`, `EI`, `H₀`, `J₀`,
  `hRange` and `hJH`. After `dsimp only` they are not needed, so this proof
  omits them.

## Original source

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean>),
SHA-256 `6d057d4d7df649ce5d67657b86688b0532b975cbc5d03be5b15582dccdc140da`.
The theorem `LocalClassFieldTheory.map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField`
has its docstring at lines 127–128, its signature at lines 129–169 and its
proof at lines 170–217. The header occupies lines 1–5.

| Original | Adapted |
| --- | --- |
| Type of `LocalClassFieldTheory.map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField` | Published `Langlands.NYLL.LocalClassFieldTheory.map_intrinsicExtensionSubgroup_eq_ambientEmbeddedFieldStatement` (U001 Statements) |
| Proof of the same theorem | `Langlands.NYLL.LocalClassFieldTheory.map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField` (this module) |
| `LocalClassFieldTheory.intrinsicExtensionSubgroup_iff_ambientEmbeddedField` (M274.001), used in the proof | `Langlands.NYLL.LocalClassFieldTheory.intrinsicExtensionSubgroup_iff_ambientEmbeddedField` (U001 Proofs) |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes: the namespace `LocalClassFieldTheory` is
prefixed with `Langlands.NYLL`; the theorem proves the published closed
proposition instead of restating its telescope; the M274.001 instance is
named `hmem`; the unused local data listed above are omitted; the source
imports are replaced by the single U001 Proofs import; all other declarations
of the source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0
notice, followed by the dated modification record. The existing
[LICENSE](../../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../../licenses/NYLL/NOTICE) are retained.

This module contains only the M274.002 proof.
