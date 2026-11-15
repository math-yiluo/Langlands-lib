# Surjectivity of the residue action of the whole Galois group: statement

This module defines one closed proposition in
`Langlands.NYLL.LocalClassFieldTheory`, the statement phase of source row
M244.004:

- `residueAlgActionOfEqTop_surjectiveStatement`, for the source theorem
  `residueAlgActionOfEqTop_surjective`.

It is a `def` returning `Prop` that packages the complete source theorem
signature. It has no proof here. A later proof will prove it under the name
`Langlands.NYLL.LocalClassFieldTheory.residueAlgActionOfEqTop_surjective`.

## The proposition

```lean
def residueAlgActionOfEqTop_surjectiveStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L]
    (A : _root_.ValuationSubring L)
    (hA : decompositionGroup K A = ⊤),
    Function.Surjective (residueAlgActionOfEqTop K A hA)
```

The definition has the two universe parameters `u` and `v` of the source,
in that order: `K` is a field in an arbitrary universe `u` and `L` a
`K`-algebra field in an independent arbitrary universe `v`. The other
binders are as follows:

- `[IsGalois K L]` says that `L / K` is a Galois extension. It may be
  infinite;
- `A` is a valuation ring of `L` (Mathlib's `ValuationSubring`);
- `hA` says that the decomposition group of `A` over `K` is the whole group.
  Here `decompositionGroup K A` is the published NYLL abbreviation (source
  row M239.001) for Mathlib's `A.decompositionSubgroup K`, the subgroup of
  automorphisms `σ` of `L ≃ₐ[K] L` with `σ • A = A`.

`residueAlgActionOfEqTop K A hA` is the published monoid homomorphism
(source row M244.003) from `L ≃ₐ[K] L` to the group of automorphisms of
`selectedResidueField A` over `decompositionResidueField K A`. Here
`selectedResidueField A` (M243.004) is the residue field of `A`, and
`decompositionResidueField K A` (M243.003) is the residue field of the
decomposition fixed subring, over which the residue field of `A` is an
algebra by the published instance M243.021. The homomorphism first views an
automorphism as an element of the decomposition group, using `hA`, and then
applies the published residue action of the decomposition group (M243.024):
an automorphism `σ` acts on residue classes by `σ` applied to
representatives in `A`.

The conclusion `Function.Surjective` says that every automorphism of the
residue field of `A` over `decompositionResidueField K A` comes from some
automorphism of `L` over `K`. So when the decomposition group is the whole
Galois group, every residue automorphism lifts to the Galois group.

### The Galois hypothesis

The binder `[IsGalois K L]` is a section variable of the source file
(line 37), and the source has no `omit [IsGalois K L] in` line before this
theorem. Lean adds a section instance variable to a theorem whose signature
mentions all its variables. The signature mentions `K` and `L`, so the
source theorem takes `[IsGalois K L]`. A private probe confirms this. It
declares a theorem with the source signature under the same section
variables, and `#check` shows that the theorem takes `[IsGalois K L]`.

The hypothesis is also used mathematically. The source proof (lines 77–85)
applies `decompositionGroupResidueAction_surjective` (source row M243.029).
That theorem is stated in a section with the variable `[IsGalois K L]`
(`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`,
lines 39–40, theorem at line 358 without an `omit` line). So the source
theorem uses it.

By contrast, the published definition `residueAlgActionOfEqTop` does not
take `[IsGalois K L]`. Lean adds to a definition only the section variables
that its signature or body uses, and neither uses `[IsGalois K L]`, as the
published M244.003 Markdown explains. The proposition therefore supplies
`[IsGalois K L]` as its own binder, at the source position after
`[Algebra K L]`.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M244.003, `LocalClassFieldTheory.residueAlgActionOfEqTop` | `Langlands.NYLL.LocalClassFieldTheory.residueAlgActionOfEqTop` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueActionIndex.U003.Definitions`) |
| M239.001, `RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup` | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup` (module `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Definitions`, imported through the M244.003 module) |

The types `selectedResidueField A` and `decompositionResidueField K A`, and
their field and algebra instances (M243.003, M243.004, M243.020, M243.021),
occur only through the type of `residueAlgActionOfEqTop`. They come from the
published module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueFields`,
imported through the M244.003 module. `ValuationSubring`, `IsGalois`,
`AlgEquiv` and `Function.Surjective` are Mathlib declarations.

## Relation to other Library and Mathlib declarations

The whole Library at commit `49668e4d9f31c1a40963e2781ac30c6a60b32704` was
searched for `residueAlgActionOfEqTop` and `decompositionGroupResidueAction`.
The only published declarations that mention them are the M244.003
definition, the M243.024 definition `decompositionGroupResidueAction`
itself, and the M249.019 statement
`Langlands.NYLL.PortInternal.M249.d019Statement` (continuity of the same
action for the separable closure of a local field). None of them states
surjectivity. In particular the source theorem M243.029,
`decompositionGroupResidueAction_surjective`, which the source proof uses,
is not yet published.

The Library has related surjectivity results for other residue maps. For
example `Langlands.LocalGalois.residueHom_surjective` (module
`Langlands.Galois.Local.SpectralProof`) is about the residue map of a
Galois extension of nonarchimedean normed fields, on the spectral valuation
rings `Langlands.LocalGalois.extensionIntegers K L` and
`Langlands.LocalGalois.baseIntegers K`. And
`Langlands.LocalGalois.absoluteResidueHom` (module
`Langlands.Galois.Local.AbsoluteDefinitions`) maps the absolute Galois
group of a local field to that of its residue field. These use different
residue fields and hypotheses, so they are different declarations.

Mathlib has the general results that the stabilizer of a prime surjects
onto the automorphisms of the residue ring:
`Ideal.Quotient.stabilizerHom_surjective` (module
`Mathlib.RingTheory.Invariant.Basic`) for a finite group, and
`Ideal.Quotient.stabilizerHom_surjective_of_profinite` (module
`Mathlib.RingTheory.Invariant.Profinite`) for a profinite group acting
continuously on a discrete ring. They are about Mathlib's
`Ideal.Quotient.stabilizerHom`, not about this NYLL homomorphism on the
whole group `L ≃ₐ[K] L`. The source proof of M243.029 applies the profinite
version to the decomposition group, and the source proof of M244.004 then
transports that surjectivity along `toDecompositionGroupOfEqTop`.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean>).
The complete file was read and its SHA-256 verified as
`985bdcfc1cc21860cc65bbb96dc92b1a0ec09dc05eadd6d4f46b4b0a551f4581`.
The M244.004 docstring is line 72 and the signature lines 73–76; the proof
is lines 77–85. The header occupies lines 1–5, the namespace line 22, the
`open` lines 24, 26 and 34, the `noncomputable section` line 30, the
`universe` line 32, the section variables lines 36–37, and the closing
`end` lines 112–113.

| Source unit and original declaration | Adapted declaration and phase |
| --- | --- |
| M244.004, `LocalClassFieldTheory.residueAlgActionOfEqTop_surjective` | `Langlands.NYLL.LocalClassFieldTheory.residueAlgActionOfEqTop_surjectiveStatement`, closed Prop target |
| Same source theorem, later proof phase | `Langlands.NYLL.LocalClassFieldTheory.residueAlgActionOfEqTop_surjective`, reserved for the proof |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 85 made these changes to the source theorem:

- The theorem becomes a Prop-valued definition with the `Statement`
  suffix. The section variables `K` and `L` and their `Field`, `Algebra`
  and `IsGalois` binders become the leading universal binders, in source
  order and with the source binder kinds (`K` explicit, `L` implicit).
  The explicit binders `A` and `hA` and the conclusion are the source text.
  The proof is omitted for the separate proof phase.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
  The source line `open HilbertRamification.ValuationSubring`, which is
  resolved inside the source's `open RamificationTheory`, becomes
  `open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`,
  so that `decompositionGroup` names the published abbreviation.
- The source imports are replaced by the Library module
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueActionIndex.U003.Definitions`.
- The `noncomputable section`, the `open RamificationTheory` and
  `open ClassFormation` lines, and all other declarations of the source
  file are omitted. The `universe u v` line is kept. The module docstring
  is a new short description of this unit.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. It also records these modifications. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only the M244.004 statement target. Its proof and the
other rows of the source file are not part of this unit.
