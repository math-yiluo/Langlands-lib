# Embedded extension quotients: action of the equivalence on `E`

This module proves the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_applyStatement`
(source row M274.007) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply`.
The theorem's type is exactly that proposition, with no parameters of its own.

It imports two modules:

- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient.U006.Proofs`,
  which proves M274.006 (`ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk`)
  and imports the published U006 Statements module containing this target;
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityCanonical.U027.Statements`,
  the published statement module of M098.027,
  `finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_applyStatement`.

The Library does not yet prove that M098.027 statement (its proof is the
separate Task 6997), so this proof proves it as a local `have`; see step 2
below. The M273.008 theorem `intrinsicBaseEquivAmbientEmbeddedField_apply_val`
(module `...BaseComparison.IntrinsicBaseEquivalence.U008.Proofs`) is
imported through the U006 Proofs module. The published Lean/Markdown pair and everything it
imports stay unchanged.

## Target

The parameters and local data are those of M274.006 (fields `K F E : Type`,
`j : E →ₐ[K] SeparableClosure K`, its restriction `i` to `F`, the two
`F`-algebra structures, `e : SeparableClosure F ≃ₐ[F] SeparableClosure K`,
`H₀`, `J₀` and `hJH`). For every
`rho : (closedFixingSubgroup K (SeparableClosure K) (AlgHom.fieldRange i)).toSubgroup`
and `x : E` the target asserts

```lean
j (ambientEmbeddedExtensionQuotientEquivGaloisGroup K F E j e
    (QuotientGroup.mk rho) x) =
  rho.1.1 (j x)
```

## Implemented proof

The proof first unfolds the statement's local data with `dsimp only`. It
then reintroduces `i` and the `F`-algebra structure on `SeparableClosure K`,
introduces `e`, `rho` and `x`, and sets

- `jF`, `j` regarded as an `F`-algebra map, and
  `jI := e.symm.toAlgHom.comp jF`;
- `psi := intrinsicBaseEquivAmbientEmbeddedField K F i e`;
- `tau := psi.symm rho`, with `hpsi : psi tau = rho`
  (`MulEquiv.apply_symm_apply`).

It has three steps:

1. `hquotient` says that the class of `rho` goes to
   `finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding F E jI (QuotientGroup.mk tau)`.
   It is proved by rewriting `rho` as `psi tau` (`← hpsi`) and applying the
   M274.006 theorem `ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk`
   to `K F E j e tau`. The goal is rewritten with `hquotient`.
2. `hmkApply` proves the published M098.027 statement
   `finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_applyStatement`
   inside this proof, by the source proof of
   `finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply`:
   - it introduces the quantified `K L`, their instances, `i`, `τ` and `x`;
   - a nested local `have baseFixing_mk_apply` states and proves the private
     source helper `baseFixingExtensionQuotientEquivGaloisGroup_mk_apply`
     (M098.026) with the source binders and proof. It unfolds the published
     `baseFixingExtensionQuotientEquivGaloisGroup` (M089.011) into
     `baseFixingExtensionQuotientEquivAmbient` (M089.009), computed on the
     class of `τ` by `rfl`, Mathlib's `InfiniteGalois.normalAutEquivQuotient`
     (`InfiniteGalois.normalAutEquivQuotient_apply`) and `AlgEquiv.autCongr`,
     and finishes with `AlgEquiv.restrictNormalHom_apply`. The source writes
     that last rewrite as a one-step `calc`; the port writes the `rw`;
   - with `E := finiteGaloisFieldRangeOfEmbedding K L i` (M090.001),
     `e := finiteGaloisFieldRangeEquivOfEmbedding K L i` (M090.002) and `g`
     the image of the class of `τ` under
     `baseFixingExtensionQuotientEquivGaloisGroup K (SeparableClosure K) E`,
     a `change` unfolds the published M090.009 definition to
     `i (((e.autCongr).symm g) x) = τ.1 (i x)`, and a three-step `calc`
     (the `autCongr` simp lemmas with `e.apply_symm_apply`, the helper, and
     `rfl`) proves it.

   The names `K`, `L`, `E`, `e`, `τ` and `x` bound inside this `have` are
   local to it. Then `haction := hmkApply F E jI tau x` is
   `jI (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding F E jI (QuotientGroup.mk tau) x) = tau.1 (jI x)`.
3. A three-step `calc` with `g := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding F E jI (QuotientGroup.mk tau)`:
   - `j (g x) = e (tau.1 (jI x))`. First, `j (g x) = e (jI (g x))`: by
     definition of `jI` the right side is `e (e.symm (j (g x)))`, which
     `AlgEquiv.apply_symm_apply` simplifies. Then apply `e` to `haction`;
   - `e (tau.1 (jI x)) = (psi tau).1.1 (j x)`: rewrite with the M273.008
     formula `(psi tau).1.1 y = e (tau.1 (e.symm y))`; the remaining goal
     holds by `rfl`, since `jI x` is by definition `e.symm (j x)`;
   - `(psi tau).1.1 (j x) = rho.1.1 (j x)`, by `rw [hpsi]`.

The proof uses only Mathlib, the M274.006 and M273.008 theorems, the
locally proved M098.027 statement and the declarations the imported modules
provide. It depends only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Relation to the original proof

The source proof (lines 640–723) has the same steps and the same `calc`.
The source also introduces the local data `EI`, `hRange`, `hJH`,
`hSourceNormal` and `hTargetNormal`. None of them appears in the terms this
proof elaborates, so they are omitted; the proof compiles without them and
without warnings.

## Original source

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean>),
SHA-256 `6d057d4d7df649ce5d67657b86688b0532b975cbc5d03be5b15582dccdc140da`.
The theorem `LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply`
has its docstring at lines 598–599, its signature at lines 600–639 and its
proof at lines 640–723. The header occupies lines 1–5.

The locally proved M098.027 statement and its helper come from
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityCanonical.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityCanonical.lean>)
at the same commit, SHA-256
`1d616a601ddd3a0a8f52c11f29d77cb1a30f9946335fa4ecef070f3a32385ad6`. The
private helper `baseFixingExtensionQuotientEquivGaloisGroup_mk_apply`
(M098.026) occupies lines 587–621 (signature 587–593, proof 594–621); the
theorem `finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply`
(M098.027) has its signature at lines 626–629 and its proof at lines
630–644.

| Original | Adapted |
| --- | --- |
| Type of `LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply` | Published `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_applyStatement` (U006 Statements) |
| Proof of the same theorem | `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply` (this module) |
| `LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk` (M274.006), used in the proof | `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk` (U006 Proofs) |
| `LocalClassFieldTheory.finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply` (M098.027), used in the proof | Local `have hmkApply` proving the published `Langlands.NYLL.LocalClassFieldTheory.finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_applyStatement` (ConcreteReciprocityCanonical U027 Statements) |
| Private `LocalClassFieldTheory.baseFixingExtensionQuotientEquivGaloisGroup_mk_apply` (M098.026), used in that proof | Nested local `have baseFixing_mk_apply` |
| `LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply_val` (M273.008), used in the proof | `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply_val` (IntrinsicBaseEquivalence U008 Proofs) |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes:

- the namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`;
- the theorem proves the published closed proposition instead of restating
  its telescope;
- the unused local data listed above are omitted;
- the source imports are replaced by the U006 Proofs module and the
  published M098.027 statement module;
- the M098.027 theorem and its private helper M098.026 are proved as local
  `have`s with their source proofs (`ConcreteReciprocityCanonical.lean`,
  helper lines 587–621, theorem proof lines 630–644), the helper's final
  one-step `calc` written as the `rw` it performs;
- all other declarations of the source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0
notice, followed by the dated modification record. The existing
[LICENSE](../../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../../licenses/NYLL/NOTICE) are retained.

This module contains only the M274.007 proof.
