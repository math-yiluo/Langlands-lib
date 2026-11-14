# The residue action of the whole Galois group

This module defines one declaration in
`Langlands.NYLL.LocalClassFieldTheory`, the adaptation of source row
M244.003:

```lean
noncomputable def residueAlgActionOfEqTop
    (A : _root_.ValuationSubring L)
    (hA : decompositionGroup K A = ⊤) :
    (L ≃ₐ[K] L) →*
      (selectedResidueField A ≃ₐ[decompositionResidueField K A]
        selectedResidueField A)
```

## Binders

The source section variables are kept:

```lean
universe u v

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
  [IsGalois K L]
```

Lean adds to a definition only the section variables that its signature or
body uses. Neither uses `[IsGalois K L]`: the two published definitions
that the body composes, `toDecompositionGroupOfEqTop` and
`decompositionGroupResidueAction`, take no Galois hypothesis either. So the
elaborated argument list is
`(K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
(A : ValuationSubring L) (hA : decompositionGroup K A = ⊤)`, with universe
parameters `u` and `v`. A private compile check printed this type with
`#check`. The source definition is elaborated the same way from the same
text.

`ValuationSubring` is Mathlib's `ValuationSubring`. The other names are
published NYLL declarations, opened through
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`:

- `decompositionGroup K A` (source row M239.001) abbreviates Mathlib's
  `A.decompositionSubgroup K`, the subgroup of `L ≃ₐ[K] L` of automorphisms
  `σ` with `σ • A = A`.
- `selectedResidueField A` (M243.004) is the residue field
  `IsLocalRing.ResidueField A` of `A`.
- `decompositionResidueField K A` (M243.003) is the quotient of the subring
  of `A` fixed by the decomposition group by the contraction of the maximal
  ideal of `A`. It is a field by the published instance M243.020, and
  `selectedResidueField A` is an algebra over it by the published instance
  M243.021.

## The definition

The hypothesis `hA` says that the decomposition group of `A` is the whole
group `L ≃ₐ[K] L`. The definition composes two published monoid
homomorphisms:

```lean
  (decompositionGroupResidueAction (K := K) A).comp
    (toDecompositionGroupOfEqTop K A hA)
```

- `toDecompositionGroupOfEqTop K A hA` (M244.001) sends
  `sigma : L ≃ₐ[K] L` to `sigma` itself, as an element of
  `decompositionGroup K A`. The membership proof uses `hA`.
- `decompositionGroupResidueAction (K := K) A` (M243.024) is the action of
  the decomposition group on the residue field of `A`. An element `σ`
  stabilizes `A` and its maximal ideal, so it induces an automorphism of
  `selectedResidueField A`. This automorphism is the identity on
  `decompositionResidueField K A`. The homomorphism is Mathlib's
  `Ideal.Quotient.stabilizerHom` composed with the identification of the
  decomposition group with the stabilizer of the maximal ideal (M243.023).

So `residueAlgActionOfEqTop K A hA sigma` is the residue automorphism that
`sigma` induces. The composite is a monoid homomorphism from the whole
Galois group. The next source row M244.004 (`residueAlgActionOfEqTop_surjective`,
not part of this unit) states that it is surjective. Its source proof uses
the surjectivity of `decompositionGroupResidueAction`.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M244.001, `LocalClassFieldTheory.toDecompositionGroupOfEqTop` | `Langlands.NYLL.LocalClassFieldTheory.toDecompositionGroupOfEqTop` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueActionIndex.U001.Definitions`) |
| M243.024, `RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroupResidueAction` | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroupResidueAction` (module `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueAction`) |
| M243.003, `RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField` | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField` (module `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Definitions`, imported through `ResidueAction`) |
| M243.004, `RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField` | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField` (same module) |
| M239.001, `RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup` | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup` (module `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Definitions`, imported through `U001.Definitions`) |

The algebra instance of `selectedResidueField A` over
`decompositionResidueField K A` (M243.021) and the field instance of
`decompositionResidueField K A` (M243.020) come from the published module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueFields`,
which `ResidueAction` imports. `ValuationSubring`, `MonoidHom.comp` and
`AlgEquiv` are Mathlib declarations.

## Relation to other Library and Mathlib declarations

The whole Library at commit `1fbff4b8a0dd4bcb09d8ea295cc0c6a1a35802af`
was searched for `residueAlgActionOfEqTop` and for
`decompositionGroupResidueAction`. The only match is the definition of
`decompositionGroupResidueAction` itself. No published declaration
provides the action of the whole Galois group on the residue field under
the hypothesis `hA`. Mathlib has no dedicated declaration for this
composite. The source introduces it as a named definition. Later source
declarations refer to it by name: M244.004 in the same file, and
declarations in the source files `LocalResidueDatum.lean` (for example
`localSeparableResidueAlgAction`) and `FixedFieldLocalData.lean`.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean>).
The complete file was read and its SHA-256 verified as
`985bdcfc1cc21860cc65bbb96dc92b1a0ec09dc05eadd6d4f46b4b0a551f4581`.
The M244.003 docstring occupies lines 61–62 and the definition lines
63–70. The header occupies lines 1–5, the namespace line 22, the `open`
lines 24, 26 and 34, the `noncomputable section` line 30, the `universe`
line 32, the section variables lines 36–37, and the closing `end` lines
112–113.

| Source unit and original declaration | Adapted declaration |
| --- | --- |
| M244.003, `LocalClassFieldTheory.residueAlgActionOfEqTop` | `Langlands.NYLL.LocalClassFieldTheory.residueAlgActionOfEqTop` |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 85 made these changes:

- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
  The source line `open HilbertRamification.ValuationSubring`, which is
  resolved inside the source's `open RamificationTheory`, becomes
  `open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`,
  so that `decompositionGroup`, `selectedResidueField`,
  `decompositionResidueField` and `decompositionGroupResidueAction` name
  the published declarations.
- The source imports are replaced by the Library modules
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueActionIndex.U001.Definitions`
  and
  `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueAction`.
- The `open RamificationTheory` and `open ClassFormation` lines, which the
  definition does not need, are omitted. All other declarations of the
  source file are omitted. The module docstring is a new short description
  of this unit.
- The `noncomputable section`, the `universe u v` line, the section
  variables, the docstring, the binders, the type and the body are the
  source text. Source lines 61–70 and the corresponding lines of the
  adapted file are byte-identical.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. It also records these modifications. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only the M244.003 definition. The other rows of the
source file are not part of this unit.
