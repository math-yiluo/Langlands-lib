# The chosen valuation rings under a finite separable extension: statements

This module defines two closed propositions in
`Langlands.NYLL.LocalClassFieldTheory`, the statement phases of source rows
M272.006 and M272.007:

- `localSeparableValuationSubring_eq_comap_finiteExtensionEquivStatement`,
  for the source theorem
  `localSeparableValuationSubring_eq_comap_finiteExtensionEquiv`;
- `localSeparableDecompositionGroup_eq_top_finiteExtensionEquivStatement`,
  for the source theorem
  `localSeparableDecompositionGroup_eq_top_finiteExtensionEquiv`.

Each is a `def` returning `Prop` that packages the complete source theorem
signature. Neither has a proof here. Later proof children will prove them
under the names
`Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_eq_comap_finiteExtensionEquiv`
and
`Langlands.NYLL.LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top_finiteExtensionEquiv`.

Both concern the valuation ring `localSeparableValuationSubring K` of
`SeparableClosure K` that the finite local reciprocity construction chooses
for a nonarchimedean local field `K` (source row M249.006, published). It is
the pullback to `SeparableClosure K` of a chosen Chevalley extension of the
valuation of `K` to `AlgebraicClosure K`.

## Common hypotheses

Both propositions universally quantify the same binders, as in the source:

```lean
(K F : Type)
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
  [Valuation.HasExtension
    (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
  (i : F →ₐ[K] SeparableClosure K)
```

So `K` and `F` are nonarchimedean local fields in `Type` (universe zero, as
in the source), `F / K` is a finite separable extension, and the valuation
of `F` extends that of `K` (Mathlib's `Valuation.HasExtension`). `i` is a
`K`-algebra embedding of `F` into `SeparableClosure K`. The propositions
then introduce, as in the source,

```lean
letI : Algebra F (SeparableClosure K) :=
  i.toRingHom.toAlgebra
letI : Algebra.IsSeparable F (SeparableClosure K) :=
  Algebra.isSeparable_tower_top_of_isSeparable
    K F (SeparableClosure K)
letI : IsSepClosure F (SeparableClosure K) :=
  ⟨inferInstance, inferInstance⟩
```

The first makes `SeparableClosure K` an `F`-algebra through `i`. The second
is Mathlib's tower lemma; the `IsScalarTower K F (SeparableClosure K)`
instance it needs is Mathlib's instance `IsScalarTower.of_algHom` for the
algebra structure of `i`. The third records that `SeparableClosure K` is a
separable closure of `F`. Neither conclusion mentions the last two local
instances. Each proposition then quantifies over an `F`-algebra
isomorphism `e : SeparableClosure F ≃ₐ[F] SeparableClosure K` for these
structures.

## The proposition `localSeparableValuationSubring_eq_comap_finiteExtensionEquivStatement`

Its conclusion is

```lean
localSeparableValuationSubring F =
  (localSeparableValuationSubring K).comap e.toRingHom
```

that is, the ring homomorphism underlying `e` pulls the chosen valuation
ring of `SeparableClosure K` back to the chosen valuation ring of
`SeparableClosure F`.

## The proposition `localSeparableDecompositionGroup_eq_top_finiteExtensionEquivStatement`

The quantified isomorphism is named `_e`, as in the source; the conclusion
does not use it. The conclusion is

```lean
decompositionGroup F (localSeparableValuationSubring K) = ⊤
```

Here `decompositionGroup F A` is the published NYLL abbreviation for
Mathlib's `A.decompositionSubgroup F`, the stabilizer of `A` in
`SeparableClosure K ≃ₐ[F] SeparableClosure K`. So the conclusion says that
every `F`-algebra automorphism of `SeparableClosure K` maps the chosen
valuation ring `localSeparableValuationSubring K` onto itself. Because the
proposition quantifies over `e`, it holds vacuously when no such `e` exists.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M249.006, `LocalClassFieldTheory.localSeparableValuationSubring` | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U006.Definitions`) |
| M239.001, `RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup` | `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup` (module `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Definitions`) |

`IsNonarchimedeanLocalField`, `ValuativeRel`, `Valuation.HasExtension`,
`SeparableClosure`, `IsSepClosure` and
`Algebra.isSeparable_tower_top_of_isSeparable` are Mathlib declarations.

## Relation to other Library and Mathlib declarations

The whole Library at commit `6948120d6f1b811bab3b7ee04997f6fba7aa9908` was
searched. No published declaration states either proposition; the only
module that mentions `localSeparableValuationSubring` is the one defining
it. Related declarations, which a proof may use or which are easy to
confuse with these ones, are the following.

- The source proofs use the NYLL theorems
  `localSeparableValuationSubring_comap_embedding` (M265.012),
  `localSeparableValuationSubring_eq_of_hasExtension` (M249.009) and
  `localSeparableDecompositionGroup_eq_top` (M249.010). None of them is
  published at that commit; none is needed to state the propositions.
- `Langlands.Galois.Local.sepClosureIntegers` (module
  `Langlands.Galois.Local.SeparableInertiaDefinitions`) is the valuation
  ring of the spectral valuation on `SeparableClosure F`, defined for a
  different construction. It is a different declaration, and no published
  result identifies it with `localSeparableValuationSubring`.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldLocalData.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldLocalData.lean>).
The complete file was read and its SHA-256 verified as
`e629ef932276f009cee72064f4b1dffe03aa262dcd391da5a6e98c4c9008f3cd`.
The M272.006 docstring occupies lines 208–210 and its signature lines
211–230; its proof occupies lines 230–258. The `open … in` prefix on lines
205–207 is used only by that proof. The M272.007 docstring occupies lines
260–262 and its signature lines 263–281; its proof occupies lines 281–326.
The header occupies lines 1–5, the module docstring lines 13–20, the
`noncomputable section` line 24, the namespace line 26 and the `open` lines
28–30.

| Source unit and original declaration | Adapted declaration and phase |
| --- | --- |
| M272.006, `LocalClassFieldTheory.localSeparableValuationSubring_eq_comap_finiteExtensionEquiv` | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_eq_comap_finiteExtensionEquivStatement`, closed Prop target |
| M272.007, `LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top_finiteExtensionEquiv` | `Langlands.NYLL.LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top_finiteExtensionEquivStatement`, closed Prop target |
| Same source theorems, later proof phase | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_eq_comap_finiteExtensionEquiv` and `Langlands.NYLL.LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top_finiteExtensionEquiv`, reserved for the proof children |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes to the two source theorems:

- Each theorem becomes a Prop-valued definition with the `Statement`
  suffix. Its explicit parameters become universal binders in the same
  order, and the proof is omitted for the separate proof phase. The binders,
  local `letI` data and conclusions are otherwise the source text.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
  The source line `open RamificationTheory.HilbertRamification.ValuationSubring`
  becomes
  `open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`,
  so that `decompositionGroup` names the published abbreviation.
- The source imports are replaced by the two Library modules listed above.
- The `noncomputable section`, the other `open` lines and the `open … in`
  prefix of M272.006, which the statements do not need, are omitted. All
  other declarations of the source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. It also records these modifications. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only the M272.006 and M272.007 statement targets. Their
proofs and the other rows of the source file are not part of this unit.
