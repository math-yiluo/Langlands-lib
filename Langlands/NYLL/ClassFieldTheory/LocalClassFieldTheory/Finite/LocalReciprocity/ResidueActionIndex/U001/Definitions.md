# The whole Galois group as decomposition group

This module defines one declaration in
`Langlands.NYLL.LocalClassFieldTheory`, the adaptation of source row
M244.001:

```lean
noncomputable def toDecompositionGroupOfEqTop
    (A : _root_.ValuationSubring L)
    (hA : decompositionGroup K A = ⊤) :
    (L ≃ₐ[K] L) →* decompositionGroup K A
```

## Binders

The source section variables are kept:

```lean
universe u v

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
  [IsGalois K L]
```

Lean adds to a definition only the section variables that its signature or
body uses. Neither uses `[IsGalois K L]`, so the elaborated argument list is
`(K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
(A : ValuationSubring L) (hA : decompositionGroup K A = ⊤)`, without a
Galois hypothesis. A private compile check confirmed this: applying the
constant to `K`, `L` and three instance arguments, the next explicit
argument expected is `A`. The source definition is elaborated the same
way from the same text. The source's next row (M244.002,
`toDecompositionGroupOfEqTop_coe`, not part of this unit) is a theorem, for
which Lean would include the instance from its signature; there the source
removes it with `omit [IsGalois K L] in`.

`ValuationSubring` is Mathlib's `ValuationSubring`. `decompositionGroup K A`
is the published NYLL abbreviation (source row M239.001) for Mathlib's
`A.decompositionSubgroup K`. This is the subgroup of `L ≃ₐ[K] L` of
automorphisms `σ` with `σ • A = A`.

## The definition

The hypothesis `hA` says that the decomposition group of `A` is the whole
group, so every automorphism stabilizes `A`. The definition is the monoid
homomorphism that sends `sigma : L ≃ₐ[K] L` to `sigma` itself, viewed as an
element of `decompositionGroup K A`:

```lean
  toFun sigma := ⟨sigma, by rw [hA]; exact Subgroup.mem_top sigma⟩
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl
```

The membership proof rewrites the goal with `hA` and uses
`Subgroup.mem_top`. The two homomorphism laws are proved by extensionality.
So the coercion of `toDecompositionGroupOfEqTop K A hA sigma` back to
`L ≃ₐ[K] L` is `sigma` by definition. The source states this as M244.002,
which is not part of this unit.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M239.001, `RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup` | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup` (module `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Definitions`) |

`ValuationSubring`, `IsGalois`, `Subgroup.mem_top` and the `MonoidHom`
structure are Mathlib declarations.

## Relation to other Library and Mathlib declarations

The whole Library at commit `6948120d6f1b811bab3b7ee04997f6fba7aa9908` was
searched for `toDecompositionGroupOfEqTop`, for other homomorphisms into a
decomposition subgroup, and for statements that a decomposition subgroup
is `⊤`. No published declaration provides this homomorphism. The closest
one is `Langlands.LocalGalois.decompositionHom` (module
`Langlands.Galois.Local.SpectralDefinitions`). It is also the identity on
underlying automorphisms, but it maps into the decomposition subgroup of
one specific valuation ring, the spectral valuation ring
`Langlands.LocalGalois.extensionIntegers K L`. Its membership proof uses
spectral norms rather than a hypothesis `hA`. It is a different
declaration.

Mathlib has no dedicated declaration for this map. The same homomorphism
could be assembled from general Mathlib operations such as
`MonoidHom.codRestrict`, but the source introduces it as a named
definition, and later NYLL rows (M244.002 onward) refer to it by name.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean>).
The complete file was read and its SHA-256 verified as
`985bdcfc1cc21860cc65bbb96dc92b1a0ec09dc05eadd6d4f46b4b0a551f4581`.
The M244.001 docstring occupies lines 39–43 and the definition lines
44–50. The header occupies lines 1–5, the namespace line 22, the `open`
lines 24, 26 and 34, the `noncomputable section` line 30, the `universe`
line 32, the section variables lines 36–37, and the closing `end` lines
112–113.

| Source unit and original declaration | Adapted declaration |
| --- | --- |
| M244.001, `LocalClassFieldTheory.toDecompositionGroupOfEqTop` | `Langlands.NYLL.LocalClassFieldTheory.toDecompositionGroupOfEqTop` |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes:

- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
  The source line `open HilbertRamification.ValuationSubring`, which is
  resolved inside the source's `open RamificationTheory`, becomes
  `open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`,
  so that `decompositionGroup` names the published abbreviation.
- The source imports are replaced by the Library module
  `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Definitions`.
- The `open RamificationTheory` and `open ClassFormation` lines, which the
  definition does not need, are omitted. All other declarations of the
  source file are omitted.
- The `noncomputable section`, the `universe u v` line, the section
  variables, the docstring, the binders, the type and the body are the
  source text.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. It also records these modifications. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only the M244.001 definition. The other rows of the
source file are not part of this unit.
