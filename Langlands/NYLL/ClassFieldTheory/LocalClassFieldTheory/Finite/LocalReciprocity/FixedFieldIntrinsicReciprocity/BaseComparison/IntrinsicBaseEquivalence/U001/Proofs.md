# Finite quotient for an embedded finite extension

This module proves the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedAbsoluteQuotientFiniteStatement`
(source row M273.001) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedAbsoluteQuotientFinite`.
The theorem's type is exactly that proposition, with no parameters of its own.

Its only import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U001.Statements`.
That published Lean/Markdown pair and everything it imports stay unchanged.

## Target

Unfolded, the target is

```lean
∀ (K F : Type) [Field K] [Field F]
    [Algebra K F] [FiniteDimensional K F]
    (i : F →ₐ[K] SeparableClosure K),
    let H₀ :=
      Langlands.NYLL.RamificationTheory.closedFixingSubgroup K (SeparableClosure K)
        (AlgHom.fieldRange i)
    Finite
      ((Langlands.NYLL.ClassFormation.baseField
          Gal(SeparableClosure K / K)).toSubgroup ⧸
        H₀.toSubgroup.subgroupOf
          (Langlands.NYLL.ClassFormation.baseField
            Gal(SeparableClosure K / K)).toSubgroup)
```

`closedFixingSubgroup K Ω M` is the closed subgroup whose underlying
subgroup is `M.fixingSubgroup`, and `baseField G` is the closed subgroup `⊤`
of `G`. So the target says that the subgroup of
`Gal(SeparableClosure K / K)` fixing the image `i(F)` has only finitely many
left cosets in the whole group.

## Implemented proof

```lean
  intro K F _ _ _ _ i
  dsimp only
  have : FiniteDimensional K (AlgHom.fieldRange i) :=
    (AlgEquiv.ofInjectiveField i).toLinearEquiv.finiteDimensional
  have hopen := (AlgHom.fieldRange i).fixingSubgroup_isOpen
  let := QuotientGroup.discreteTopology hopen
  have : Finite (Gal(SeparableClosure K / K) ⧸ (AlgHom.fieldRange i).fixingSubgroup) :=
    finite_of_compact_of_discrete
  have : (AlgHom.fieldRange i).fixingSubgroup.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  change Finite (_ ⧸ (AlgHom.fieldRange i).fixingSubgroup.subgroupOf _)
  exact Subgroup.finite_quotient_of_finiteIndex
```

1. After introducing the seven binders, `dsimp only` substitutes the `let`
   for `H₀`.
2. The image `i(F)` is `K`-isomorphic to `F` by Mathlib's
   `AlgEquiv.ofInjectiveField i`, so it is finite-dimensional over `K`.
3. Mathlib's `IntermediateField.fixingSubgroup_isOpen`
   (`Mathlib/FieldTheory/KrullTopology.lean`) says that the fixing subgroup
   of a finite-dimensional intermediate field is open in the Krull topology.
4. The quotient of a topological group by an open subgroup is discrete
   (`QuotientGroup.discreteTopology`), and `Gal(SeparableClosure K / K)` is
   compact (Mathlib's instance `CompactSpace Gal(K/k)` for `IsGalois k K`,
   `Mathlib/FieldTheory/Galois/Profinite.lean`). The quotient is the image
   of a compact space, hence compact, so `finite_of_compact_of_discrete`
   makes it finite.
5. `Subgroup.finiteIndex_of_finite_quotient` turns this into
   `(AlgHom.fieldRange i).fixingSubgroup.FiniteIndex`.
6. The `change` unfolds `closedFixingSubgroup` and the closed subgroup
   coercion, so the goal reads
   `Finite (⊤ ⧸ (AlgHom.fieldRange i).fixingSubgroup.subgroupOf ⊤)`.
   Mathlib's instance `Subgroup.instFiniteIndex_subgroupOf` gives the
   relative subgroup finite index, and
   `Subgroup.finite_quotient_of_finiteIndex` closes the goal.

The proof uses only Mathlib and the definitions the statement already
imports. No extra hypothesis or exported instance or auxiliary declaration is added;
the finiteness and topology instances are local to this proof.

## Relation to the original proof

The original source (lines 43–77) proves the theorem by transport: it
compares the base `baseField G` with the closed fixing subgroup of the
bottom intermediate field `⊥` through
`closedFixingSubgroup_bot_eq_baseField`, obtains finiteness for the fixing
subgroup of `⊥` by an instance search over the source's own instances, and
moves it along `Equiv.cast`. The implemented proof avoids those source
helpers and argues directly with Mathlib's Krull topology.

## Original source

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/IntrinsicBaseEquivalence.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/IntrinsicBaseEquivalence.lean>),
SHA-256 `0c4403626ce06952a02d1bd927112542e4f69466ca939a1d0896195d94ef5800`.
The theorem `LocalClassFieldTheory.ambientEmbeddedAbsoluteQuotientFinite`
has its docstring at lines 28–29, its signature at lines 30–42 and its proof
at lines 43–77. The header occupies lines 1–5.

| Original | Adapted |
| --- | --- |
| Type of `LocalClassFieldTheory.ambientEmbeddedAbsoluteQuotientFinite` | Published `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedAbsoluteQuotientFiniteStatement` (U001 Statements) |
| Proof of the same theorem | `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedAbsoluteQuotientFinite` (this module), by a different route |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes: the namespace `LocalClassFieldTheory` is
prefixed with `Langlands.NYLL`; the theorem proves the published closed
proposition instead of restating its telescope; the proof is replaced as
described above; the source imports are replaced by the single U001
Statements import; all other declarations of the source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0
notice, followed by the dated modification record. The existing
[LICENSE](../../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../../licenses/NYLL/NOTICE) are retained.

This module contains only the M273.001 proof.

Worker 226 adopted the shared draft by Worker 57 for this proof task,
checked the cited original proof and retained source and adaptation attribution.
