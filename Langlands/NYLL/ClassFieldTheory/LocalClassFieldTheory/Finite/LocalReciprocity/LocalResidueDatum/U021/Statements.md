# Surjectivity of the continuous local residue action: statement

This module defines one closed proposition in
`Langlands.NYLL.LocalClassFieldTheory`. It is the statement phase of source
row M249.021:

- `localSeparableResidueAlgAction_surjectiveStatement`, for the source
  theorem `localSeparableResidueAlgAction_surjective`.

It is a `def` returning `Prop` that packages the complete source theorem
signature. It has no proof here. A later proof will prove it under the name
`Langlands.NYLL.LocalClassFieldTheory.localSeparableResidueAlgAction_surjective`.

## The proposition

```lean
def localSeparableResidueAlgAction_surjectiveStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    Function.Surjective (localSeparableResidueAlgAction K)
```

The definition has no universe parameters. As in the source, `K` is a field
in `Type` with Mathlib's `ValuativeRel` and `TopologicalSpace` structures,
and `IsNonarchimedeanLocalField K` says that `K` is a nonarchimedean local
field. These are the source section variables (lines 45–46). They become the
leading universal binders, in source order and with the source binder kinds.

`localSeparableResidueAlgAction K` is the definition published from source
row M249.020 (module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U020.Definitions`).
It is a continuous monoid homomorphism (Mathlib's `→ₜ*`)

```lean
Gal(SeparableClosure K / K) →ₜ*
  (selectedResidueField (localSeparableValuationSubring K) ≃ₐ[
    decompositionResidueField K (localSeparableValuationSubring K)]
      selectedResidueField (localSeparableValuationSubring K))
```

Here:

- `Gal(SeparableClosure K / K)` is Mathlib's notation for the absolute
  Galois group `SeparableClosure K ≃ₐ[K] SeparableClosure K` of `K`;
- `localSeparableValuationSubring K` (M249.006) is the valuation ring `A` of
  `SeparableClosure K` chosen by finite local reciprocity. Its decomposition
  group over `K` is the whole Galois group (published theorem
  `localSeparableDecompositionGroup_eq_top`, M249.010);
- `selectedResidueField A` (M243.004) is the residue field `Ω` of `A`, and
  `decompositionResidueField K A` (M243.003) is the base residue field `κ`,
  the residue field of the subring of `A` fixed by the decomposition group.
  The `κ`-algebra structure on `Ω` is the published instance M243.021.

The underlying monoid homomorphism of `localSeparableResidueAlgAction K` is
the published `residueAlgActionOfEqTop K A (localSeparableDecompositionGroup_eq_top K)`
(M244.003). An automorphism `σ` of `SeparableClosure K` maps `A` onto itself
and acts on a residue class by applying `σ` to a representative in `A`.

In the statement, `Function.Surjective (localSeparableResidueAlgAction K)`
applies `Function.Surjective` to the function underlying the continuous
monoid homomorphism, through Mathlib's coercion to functions. The
proposition says that every automorphism of `Ω` over `κ` is the residue
action of some element of the absolute Galois group of `K`. This is the
source docstring: every automorphism of the selected residue extension lifts
to the separable Galois group.

### Binders

The source theorem has no explicit binders and the source has no `omit`
line before it. Its signature mentions `K` and, through
`localSeparableResidueAlgAction K`, all four instance variables. So the
source theorem takes exactly the section variables of lines 45–46, and the
proposition binds exactly these. A private probe confirms it. A theorem with
the source signature, declared under the same section variables, has type
`∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K], ...` by `#check`.

The source file also declares two local instances (lines 47–53), the algebra
`SeparableClosure K → AlgebraicClosure K` and a scalar tower. The statement
does not mention `AlgebraicClosure K`, so they are not used and are omitted.

## Expected proof

The source proof (lines 396–398) applies the M244.004 theorem
`residueAlgActionOfEqTop_surjective` to `localSeparableValuationSubring K`
and `localSeparableDecompositionGroup_eq_top K`. A private probe replays it
against this proposition: given the published M244.004 target
`Langlands.NYLL.LocalClassFieldTheory.residueAlgActionOfEqTop_surjectiveStatement`
at universes `0` and `0`, the term

```lean
fun K _ _ _ _ => h244 K
  (localSeparableValuationSubring K)
  (localSeparableDecompositionGroup_eq_top K)
```

proves the proposition. So the coercion of the continuous homomorphism agrees
definitionally with that of its underlying monoid homomorphism. This probe is
development evidence only. The proof is a separate unit and is not part of
this module.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M249.020, `LocalClassFieldTheory.localSeparableResidueAlgAction` | `Langlands.NYLL.LocalClassFieldTheory.localSeparableResidueAlgAction` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U020.Definitions`) |

The other declarations named above occur only through the type of
`localSeparableResidueAlgAction`. They are imported through the M249.020
module: `localSeparableValuationSubring` (M249.006, module
`...LocalReciprocity.LocalResidueDatum.U006.Definitions`),
`localSeparableDecompositionGroup_eq_top` (M249.010, module
`...LocalReciprocity.LocalResidueDatum.U010.Proofs`),
`residueAlgActionOfEqTop` (M244.003, module
`...LocalReciprocity.ResidueActionIndex.U003.Definitions`), and
`selectedResidueField`, `decompositionResidueField` with their field and
algebra instances (M243.003, M243.004, M243.020, M243.021, namespace
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`,
module
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueFields`).
`SeparableClosure`, `AlgEquiv`, `ContinuousMonoidHom`, `ValuativeRel`,
`IsNonarchimedeanLocalField` and `Function.Surjective` are Mathlib
declarations.

## Relation to other Library and Mathlib declarations

The whole Library at commit `fab9caeae532b7a65e67e702bcab72d3194371ae` was
searched for `localSeparableResidueAlgAction` and `residueAlgActionOfEqTop`.
At that commit the only declarations that mention them are the M244.003
definition, the M249.019 statement
`Langlands.NYLL.PortInternal.M249.d019Statement` (continuity of the same
action), the M249.020 definition `localSeparableResidueAlgAction` itself,
and the M244.004 statement `residueAlgActionOfEqTop_surjectiveStatement`
(module `...LocalReciprocity.ResidueActionIndex.U004.Statements`). The
M244.004 statement is surjectivity of `residueAlgActionOfEqTop` for every
Galois extension whose decomposition group is everything, a general
proposition about arbitrary extensions with no proof yet. None of them
states this proposition, which is surjectivity of the continuous
homomorphism `localSeparableResidueAlgAction K` for a local field `K`.

The Library has a related result about another map.
`Langlands.LocalGalois.absoluteResidueHom_surjective` (module
`Langlands.Galois.Local.AbsoluteProof`) says that
`Langlands.LocalGalois.absoluteResidueHom K`, a monoid homomorphism from the
absolute Galois group `Field.absoluteGaloisGroup K` (built from
`AlgebraicClosure K`) to the absolute Galois group of the residue field
`𝓀[K]`, is surjective. That map uses the spectral valuation ring of
`AlgebraicClosure K` and is stated under the extra hypothesis
`[CharZero K]`. So it has a different domain, codomain and hypotheses, and
it is a different declaration.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean>).
The complete file was read and its SHA-256 verified as
`be13bf4f92820faee2f89e127b56f6bbf23a8f5a4fe93fd2e5e58745ca7d4396`.
The M249.021 docstring is line 393 and the signature lines 394–395; the
proof is lines 396–398. The header occupies lines 1–5, the namespace line
31, the `open` lines 33, 35 and 41–43, the `noncomputable section` line 39,
the section variables lines 45–46, the local instances lines 47–53, and the
closing `end` lines 443–444.

| Source unit and original declaration | Adapted declaration and phase |
| --- | --- |
| M249.021, `LocalClassFieldTheory.localSeparableResidueAlgAction_surjective` | `Langlands.NYLL.LocalClassFieldTheory.localSeparableResidueAlgAction_surjectiveStatement`, closed Prop target |
| Same source theorem, later proof phase | `Langlands.NYLL.LocalClassFieldTheory.localSeparableResidueAlgAction_surjective`, reserved for the proof |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 85 made these changes to the source theorem:

- The theorem becomes a Prop-valued definition with the `Statement`
  suffix. The section variable `K` and its four instance binders become the
  leading universal binders, in source order and with the source binder
  kinds. The conclusion is the source text. The proof is omitted for the
  separate proof phase.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
- The source imports are replaced by the Library module
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U020.Definitions`.
- The `noncomputable section`, all `open` lines (the statement names only
  declarations of its own namespace and Mathlib), the two local instances
  and all other declarations of the source file are omitted. The module
  docstring is a new short description of this unit. The declaration
  docstring names the stated theorem and keeps the source docstring.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. It also records these modifications. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only the M249.021 statement target. Its proof and the
other rows of the source file are not part of this unit.
