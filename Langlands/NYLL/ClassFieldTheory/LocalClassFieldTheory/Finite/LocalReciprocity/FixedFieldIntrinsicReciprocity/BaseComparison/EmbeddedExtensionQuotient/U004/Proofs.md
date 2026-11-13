# Finiteness of embedded extension quotients

This module proves the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotient_finiteStatement`
(source row M274.004) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotient_finite`.
The theorem's type is exactly that proposition, with no parameters of its own.

Its only import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient.U003.Statements`,
the module where the statement is published together with M274.003. That
published Lean/Markdown pair and everything it imports stay unchanged. The
proof is placed in its own `U004` module so that each proof is a separate
unit.

## Target

Unfolded, the target is

```lean
∀ (K F E : Type) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K),
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ _e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      let H₀ :=
        Langlands.NYLL.RamificationTheory.closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      let J₀ :=
        Langlands.NYLL.RamificationTheory.closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange j)
      Finite
        (H₀.toSubgroup ⧸ J₀.toSubgroup.subgroupOf H₀.toSubgroup)
```

`closedFixingSubgroup K Ω M` is the closed subgroup whose underlying
subgroup is `M.fixingSubgroup`. So the target says that the subgroup of
`Gal(SeparableClosure K / K)` fixing `j(E)` has only finitely many left
cosets inside the subgroup `H₀` fixing `i(F)`.

## Implemented proof

```lean
  intro K F E _ _ _ _ _ _ _ _ _ _ _ j i _e H₀ J₀
  have : FiniteDimensional K E := Module.Finite.trans F E
  have : FiniteDimensional K (AlgHom.fieldRange j) :=
    (AlgEquiv.ofInjectiveField j).toLinearEquiv.finiteDimensional
  have hopen := (AlgHom.fieldRange j).fixingSubgroup_isOpen
  let := QuotientGroup.discreteTopology hopen
  have : Finite (Gal(SeparableClosure K / K) ⧸ (AlgHom.fieldRange j).fixingSubgroup) :=
    finite_of_compact_of_discrete
  have : (AlgHom.fieldRange j).fixingSubgroup.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  change Finite (_ ⧸ (AlgHom.fieldRange j).fixingSubgroup.subgroupOf _)
  exact Subgroup.finite_quotient_of_finiteIndex
```

1. The introductions are `K F E`, the eleven instance arguments, `j`, `i`,
   `_e`, `H₀` and `J₀`. The two `letI` algebra instances of the statement
   are inlined into the goal, so they are not introduced. The proof does not
   use `_e` or the hypothesis `Algebra.IsSeparable K F`.
2. `E` is finite-dimensional over `K` by the tower `K ⊆ F ⊆ E`
   (`Module.Finite.trans`), and its image `j(E)` is `K`-isomorphic to `E`
   (`AlgEquiv.ofInjectiveField j`), so it is finite-dimensional too.
3. Mathlib's `IntermediateField.fixingSubgroup_isOpen`
   (`Mathlib/FieldTheory/KrullTopology.lean`) makes the fixing subgroup of
   `j(E)` open in the Krull topology. The quotient by an open subgroup is
   discrete (`QuotientGroup.discreteTopology`), and
   `Gal(SeparableClosure K / K)` is compact (Mathlib's instance
   `CompactSpace Gal(K/k)` for `IsGalois k K`,
   `Mathlib/FieldTheory/Galois/Profinite.lean`). So the quotient is finite
   by `finite_of_compact_of_discrete`, and
   `Subgroup.finiteIndex_of_finite_quotient` gives finite index.
4. The `change` unfolds `closedFixingSubgroup` for `J₀`, so the goal reads
   `Finite (H₀ ⧸ (AlgHom.fieldRange j).fixingSubgroup.subgroupOf H₀)`.
   Mathlib's instance `Subgroup.instFiniteIndex_subgroupOf` gives the
   relative subgroup finite index in `H₀`, and
   `Subgroup.finite_quotient_of_finiteIndex` closes the goal.

The proof uses only Mathlib and the definitions the statement already
imports. It does not use the normality theorem M274.003. No hypothesis,
instance or auxiliary declaration is added.

## Relation to the original proof

The original source (lines 333–392) proves the theorem by transport: it
builds the abstract finite Galois extension
`finiteGaloisAbstractExtensionOfEmbedding F E jI` over the intrinsic base of
`F`, takes its finiteness field `EI.finite`, and moves it to the ambient
quotient along `QuotientGroup.congr` for the isomorphism
`intrinsicBaseEquivAmbientEmbeddedField`, using
`map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField`. The source
statement also installs the normality from M274.003 as a local instance,
which the published statement omits because the conclusion does not use
it. The implemented proof avoids the source constructions and argues
directly with Mathlib's Krull topology.

## Original source

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean>),
SHA-256 `6d057d4d7df649ce5d67657b86688b0532b975cbc5d03be5b15582dccdc140da`.
The theorem `LocalClassFieldTheory.ambientEmbeddedExtensionQuotient_finite`
has its docstring at lines 298–299, its signature at lines 300–332 and its
proof at lines 333–392. The header occupies lines 1–5.

| Original | Adapted |
| --- | --- |
| Type of `LocalClassFieldTheory.ambientEmbeddedExtensionQuotient_finite` | Published `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotient_finiteStatement` (U003 Statements) |
| Proof of the same theorem | `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotient_finite` (this module), by a different route |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes: the namespace `LocalClassFieldTheory` is
prefixed with `Langlands.NYLL`; the theorem proves the published closed
proposition instead of restating its telescope; the proof is replaced as
described above; the source imports are replaced by the single U003
Statements import; all other declarations of the source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0
notice, followed by the dated modification record. The existing
[LICENSE](../../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../../licenses/NYLL/NOTICE) are retained.

This module contains only the M274.004 proof.
