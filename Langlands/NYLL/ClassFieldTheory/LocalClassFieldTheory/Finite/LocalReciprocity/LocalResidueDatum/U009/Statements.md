# Uniqueness of the chosen valuation ring of the separable closure: statements

This module defines two closed propositions in
`Langlands.NYLL.LocalClassFieldTheory`, the statement phases of source rows
M249.009 and M249.010:

- `localSeparableValuationSubring_eq_of_hasExtensionStatement`, for the
  source theorem `localSeparableValuationSubring_eq_of_hasExtension`;
- `localSeparableDecompositionGroup_eq_topStatement`, for the source theorem
  `localSeparableDecompositionGroup_eq_top`.

Each is a `def` returning `Prop` that packages the complete source theorem
signature. Neither has a proof here. Later proof children will prove them
under the names
`Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_eq_of_hasExtension`
and
`Langlands.NYLL.LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top`.

Both concern the valuation ring `localSeparableValuationSubring K` of
`SeparableClosure K` that the finite local reciprocity construction chooses
for a nonarchimedean local field `K` (source row M249.006, published). It is
the pullback to `SeparableClosure K` of a chosen Chevalley extension of the
canonical discrete valuation of `K` to `AlgebraicClosure K`.

## Common hypotheses

In the source, both theorems depend on the section variables

```lean
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
```

Each proposition quantifies these first, in the same order, as
`∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K], …`. So `K` is a nonarchimedean local field
in `Type` (universe zero, as in the source).

## The proposition `localSeparableValuationSubring_eq_of_hasExtensionStatement`

After `K`, it quantifies, as in the source signature,

```lean
(B : ValuationSubring (SeparableClosure K))
[(localCompleteDVF K).valuation.HasExtension B.valuation]
```

and concludes

```lean
localSeparableValuationSubring K = B
```

Here `ValuationSubring` is Mathlib's `ValuationSubring`, and
`localCompleteDVF K` is the published NYLL packaging (source row M248.001)
of the canonical valuation of `K` as a complete discrete valuation field.
Its field `valuation` is that valuation on `K`. The instance binder is
Mathlib's `Valuation.HasExtension` for the `K`-algebra `SeparableClosure K`:
the valuation of `B` restricts along `algebraMap K (SeparableClosure K)` to
a valuation equivalent to the valuation of `localCompleteDVF K`. The
proposition says that every valuation ring `B` of `SeparableClosure K` with
this property is the chosen valuation ring. So the choice made in M249.006
does not depend on the Chevalley extension that was chosen.

## The proposition `localSeparableDecompositionGroup_eq_topStatement`

It has no further binders after `K`, and its conclusion is

```lean
decompositionGroup K (localSeparableValuationSubring K) = ⊤
```

Here `decompositionGroup K A` is the published NYLL abbreviation (source
row M239.001) for Mathlib's `A.decompositionSubgroup K`, the stabilizer of
`A` in `SeparableClosure K ≃ₐ[K] SeparableClosure K`. So the conclusion
says that every `K`-algebra automorphism of `SeparableClosure K` maps the
chosen valuation ring onto itself.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M249.006, `LocalClassFieldTheory.localSeparableValuationSubring` | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U006.Definitions`) |
| M248.001, `LocalFieldTheory.localCompleteDVF` | `Langlands.NYLL.LocalFieldTheory.localCompleteDVF` (module `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.Canonical`, imported through the M249.006 module) |
| M239.001, `RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup` | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup` (module `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Definitions`) |

`IsNonarchimedeanLocalField`, `ValuativeRel`, `ValuationSubring`,
`Valuation.HasExtension` and `SeparableClosure` are Mathlib declarations.

## Relation to other Library and Mathlib declarations

The whole Library at commit `6948120d6f1b811bab3b7ee04997f6fba7aa9908` was
searched for both source names, for `localSeparableValuationSubring`, and
for statements that a decomposition subgroup is `⊤`. No published
declaration states either proposition. The only Library module that
mentions `localSeparableValuationSubring` is the one defining it. Related
declarations are the following.

- `Langlands.LocalGalois.decompositionHom` (module
  `Langlands.Galois.Local.SpectralDefinitions`) maps every automorphism of
  an algebraic extension `L` of a complete nonarchimedean normed field `K`
  into the decomposition subgroup of `Langlands.LocalGalois.extensionIntegers K L`,
  the valuation ring of the spectral valuation on `L`. That is a different
  valuation ring under different hypotheses, and it does not mention
  `localSeparableValuationSubring`.
- `Langlands.LocalGalois.Separable.sepClosureIntegers` (module
  `Langlands.Galois.Local.SeparableInertiaDefinitions`) is
  `extensionIntegers F (SeparableClosure F)`, the spectral valuation ring
  on a separable closure, defined for a different construction. No
  published result identifies it with `localSeparableValuationSubring`.
- The source proofs use the NYLL rows
  `exists_integralClosure_standard_fundamental_identity` (M245.018),
  `target_valuationSubring_eq_of_finite_separable`,
  `restrictIntermediateField_hasExtension`,
  `valuationSubring_isScalarTower_of_hasExtension` and `smul_hasExtension`.
  None of them is needed to state the propositions.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean>).
The complete file was read and its SHA-256 verified as
`be13bf4f92820faee2f89e127b56f6bbf23a8f5a4fe93fd2e5e58745ca7d4396`.
The M249.009 docstring occupies lines 115–117 and its signature lines
118–121; its proof occupies lines 121–159. The M249.010 docstring occupies
lines 161–162 and its signature lines 163–164; its proof occupies lines
164–174. The header occupies lines 1–5, the namespace line 31, the `open`
lines 33, 35 and 41–43, the `noncomputable section` line 39 and the
section variables lines 45–46.

| Source unit and original declaration | Adapted declaration and phase |
| --- | --- |
| M249.009, `LocalClassFieldTheory.localSeparableValuationSubring_eq_of_hasExtension` | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_eq_of_hasExtensionStatement`, closed Prop target |
| M249.010, `LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top` | `Langlands.NYLL.LocalClassFieldTheory.localSeparableDecompositionGroup_eq_topStatement`, closed Prop target |
| Same source theorems, later proof phase | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_eq_of_hasExtension` and `Langlands.NYLL.LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top`, reserved for the proof children |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes to the two source theorems:

- Each theorem becomes a Prop-valued definition with the `Statement`
  suffix. The section variable `K` and its four instance binders become the
  leading universal binders; the explicit `B` and the `HasExtension`
  instance binder of M249.009 follow in source order. The proofs are
  omitted for the separate proof phase. The binders and conclusions are
  otherwise the source text.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
  Of the source `open` lines, only two are kept, with the same prefix:
  `open Langlands.NYLL.LocalFieldTheory` (from source line 35), so that
  `localCompleteDVF` names the published definition, and
  `open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`
  (source line 42), so that `decompositionGroup` names the published
  abbreviation.
- The source imports are replaced by the two Library modules
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U006.Definitions`
  and
  `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Definitions`.
- The `noncomputable section`, the other `open` lines and all other
  declarations of the source file are omitted. The source file's two local
  instances (M249.001/.002, which make `AlgebraicClosure K` an algebra over
  `SeparableClosure K`) are not used by either statement.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. It also records these modifications. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only the M249.009 and M249.010 statement targets. Their
proofs and the other rows of the source file are not part of this unit.
