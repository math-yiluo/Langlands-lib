# Compatible field equivalences preserve valuation subrings: statement

This module defines one closed proposition:

- `Langlands.NYLL.LocalClassFieldTheory.valuationSubring_mem_iff_of_separableClosureRingEquivStatement : Prop`,
  the statement phase of source row M283.005, the theorem
  `LocalClassFieldTheory.valuationSubring_mem_iff_of_separableClosureRingEquiv`.

The module contains no proof. A separate proof child will prove it under the
name `Langlands.NYLL.LocalClassFieldTheory.valuationSubring_mem_iff_of_separableClosureRingEquiv`.

## Complete closed telescope

The definition has no parameters or universe variables. Its body is

```lean
∀ (F K L M : Type)
  [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [Algebra F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L]
  [Valuation.HasExtension
    (ValuativeRel.valuation F) (ValuativeRel.valuation L)]
  [Field M] [ValuativeRel M] [Algebra K M]
  [FiniteDimensional K M] [Algebra.IsSeparable K M]
  [Valuation.HasExtension
    (ValuativeRel.valuation K) (ValuativeRel.valuation M)]
  (jL : L →ₐ[F] SeparableClosure F)
  (jM : M →ₐ[K] SeparableClosure K)
  (psi : SeparableClosure F ≃+* SeparableClosure K),
  localSeparableValuationSubring F =
      (localSeparableValuationSubring K).comap psi.toRingHom →
    ∀ (phi : L ≃+* M),
      (∀ x : L, jM (phi x) = psi (jL x)) →
        ∀ (x : L),
          x ∈ (ValuativeRel.valuation L).valuationSubring ↔
            phi x ∈ (ValuativeRel.valuation M).valuationSubring
```

It has the thirty-one binders of the source theorem, in the source order:

| Binder | Kind and meaning |
| --- | --- |
| `F K L M : Type` | Explicit types, in universe zero as in the source |
| `[Field F]`, `[ValuativeRel F]`, `[TopologicalSpace F]`, `[IsNonarchimedeanLocalField F]` | Instance-implicit structures making `F` a nonarchimedean local field |
| `[Field K]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]` | The same four structures on `K` |
| `[Field L]`, `[ValuativeRel L]`, `[Algebra F L]` | Instance-implicit: `L` is a field with a valuative relation and an `F`-algebra |
| `[FiniteDimensional F L]`, `[Algebra.IsSeparable F L]` | Instance-implicit: `L` is finite and separable over `F` |
| `[Valuation.HasExtension (ValuativeRel.valuation F) (ValuativeRel.valuation L)]` | Instance-implicit: the valuation of `L` extends that of `F` (Mathlib: the valuation of `F` is equivalent to the pullback of that of `L` along `algebraMap F L`) |
| `[Field M]`, `[ValuativeRel M]`, `[Algebra K M]`, `[FiniteDimensional K M]`, `[Algebra.IsSeparable K M]`, `[Valuation.HasExtension …]` | The same six structures for `M` over `K` |
| `(jL : L →ₐ[F] SeparableClosure F)` | Explicit `F`-embedding of `L` into Mathlib's separable closure of `F` |
| `(jM : M →ₐ[K] SeparableClosure K)` | Explicit `K`-embedding of `M` into the separable closure of `K` |
| `(psi : SeparableClosure F ≃+* SeparableClosure K)` | Explicit ring equivalence of the two separable closures |
| premise (source `hpsi`) | `psi` matches the chosen valuation subrings: `localSeparableValuationSubring F` is the preimage of `localSeparableValuationSubring K` under `psi` |
| `(phi : L ≃+* M)` | Explicit ring equivalence of the two extensions |
| premise (source `hphi`) | `phi` is compatible with `psi` through the embeddings: `jM (phi x) = psi (jL x)` for all `x : L` |
| `(x : L)` | Explicit element |

Every binder is quantified inside the proposition. The source names the two
hypotheses `hpsi` and `hphi`; the conclusion mentions neither, so they appear
here as unnamed implication premises in exactly their source positions. This
changes no binder kind: both were explicit arguments in the source, and an
implication premise is an explicit, unnamed binder.

## Meaning

`Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring K :
ValuationSubring (SeparableClosure K)` is the published adaptation of source
row M249.006: the pullback to `SeparableClosure K` of a fixed Chevalley
extension, to `AlgebraicClosure K`, of the canonical valuation ring of the
nonarchimedean local field `K`. It is the valuation choice of the finite local
reciprocity construction.

The proposition says the following. Let `L/F` and `M/K` be finite separable
extensions of nonarchimedean local fields whose valuations extend the base
valuations, embedded into the separable closures by `jL` and `jM`. Let `psi`
identify the separable closures so that the chosen valuation subring of the
separable closure of `F` is the preimage of that of `K`, and let `phi : L ≃+* M`
agree with `psi` through the embeddings. Then for every `x : L`, `x` lies in
the valuation subring of `L` exactly when `phi x` lies in the valuation subring
of `M`. In other words `phi` carries the integers of `L` onto the integers of
`M`.

This is the hypothesis `hmem` required by the published
`chosenValuationOneUnitOfRingEquiv` (M283.002) and by the published statements
of M283.001, M283.003 and M283.004.

## Reused declarations

| Source unit and original declaration | Declaration used |
| --- | --- |
| M249.006, `LocalClassFieldTheory.localSeparableValuationSubring` | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U006.Definitions` (imported) |
| Mathlib `Valuation.HasExtension` | Module `Mathlib.RingTheory.Valuation.Extension` (imported explicitly) |
| Mathlib `IsNonarchimedeanLocalField`, `ValuativeRel.valuation`, `Valuation.valuationSubring`, `ValuationSubring.comap`, `SeparableClosure`, `Algebra.IsSeparable`, `FiniteDimensional`, `AlgHom`, `RingEquiv` | Used unchanged, through the imports' Mathlib closure |

The source's open namespace `LocalClassFieldTheory` corresponds to the
adaptation's namespace `Langlands.NYLL.LocalClassFieldTheory`, so
`localSeparableValuationSubring` resolves to the published declaration
without a qualified name.

## Library search

The whole Library at commit `0c3f30c24701c74d5474fca3fbb5324a99aa1d58` was
searched for `valuationSubring_mem_iff_of_separableClosureRingEquiv`, for every
use of `localSeparableValuationSubring`, and for ring equivalences of separable
closures (`SeparableClosure _ ≃+* SeparableClosure _`). The only use of
`localSeparableValuationSubring` is its definition, and the only file with a
separable-closure equivalence (`BaseComparison/IntrinsicBaseEquivalence/U004`)
defines Galois-group transports, not a statement about valuation subrings.
So nothing in the Library already covers M283.005.

## Original source

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean>).
The complete file was read; its SHA-256 is
`b430f3810416cb42cc7c61df63be3691b219a5fe39c0bc7c0c2a74292298bfa0`.
The header is at lines 1–5, the imports at 7–8, the module docstring at
10–16, `noncomputable section` at 20, the namespace at 22 and the `open`
lines at 24–26.

| Source unit and original declaration | Source lines | Adapted declaration |
| --- | --- | --- |
| M283.005, `LocalClassFieldTheory.valuationSubring_mem_iff_of_separableClosureRingEquiv` | docstring 144–146, signature 147–171, proof 172–185 (omitted) | `Langlands.NYLL.LocalClassFieldTheory.valuationSubring_mem_iff_of_separableClosureRingEquivStatement` |

The source signature is

```lean
theorem valuationSubring_mem_iff_of_separableClosureRingEquiv
    (F K L M : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [Algebra F L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L]
    [Valuation.HasExtension
      (ValuativeRel.valuation F) (ValuativeRel.valuation L)]
    [Field M] [ValuativeRel M] [Algebra K M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation M)]
    (jL : L →ₐ[F] SeparableClosure F)
    (jM : M →ₐ[K] SeparableClosure K)
    (psi : SeparableClosure F ≃+* SeparableClosure K)
    (hpsi :
      localSeparableValuationSubring F =
        (localSeparableValuationSubring K).comap psi.toRingHom)
    (phi : L ≃+* M)
    (hphi : ∀ x : L, jM (phi x) = psi (jL x))
    (x : L) :
    x ∈ (ValuativeRel.valuation L).valuationSubring ↔
      phi x ∈ (ValuativeRel.valuation M).valuationSubring
```

The source proof (omitted here) rewrites both valuation subrings as preimages
of the chosen separable-closure valuation subrings along `jL` and `jM`, using
the source theorem `localSeparableValuationSubring_comap_embedding` (source
row M265.012), and then uses `hphi` and `hpsi`. The proof phase therefore needs
the published proof of M265.012.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 56 extracted the asserted type directly from the pinned original on
13 November 2026 and made these changes:

- The theorem becomes a Prop-valued definition with the `Statement` suffix.
  All thirty-one binders move inside the proposition in the same order, with
  the same binder kinds and the source's universe-zero `Type`. The proof is
  omitted for the separate proof phase.
- The unreferenced hypotheses `hpsi` and `hphi` become unnamed implication
  premises in their source positions.
- The namespace `LocalClassFieldTheory` gets the `Langlands.NYLL` prefix, and
  the unused `open` lines are omitted.
- The source imports (`Mathlib.FieldTheory.Galois.Basic` and the NYLL
  `EmbeddedFrobeniusTransport` module) are replaced by the published module
  defining `localSeparableValuationSubring` and Mathlib's
  `Mathlib.RingTheory.Valuation.Extension`, which defines
  `Valuation.HasExtension`.
- The `noncomputable section` and all other declarations of the source file
  are omitted. A proposition definition needs no noncomputable section.

The original docstring is kept on the definition. No instance or simp
attribute is installed. No shared draft or other worker's unpublished work
was reused.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance, and the Apache-2.0
notice, followed by a dated modification record. The existing
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Scope

This unit contains only this statement. Its truth proof belongs to a separate
proof unit published after the statement is accepted and after the proof of
M265.012 is in the Library. The theorem `normUnits_mapEquiv` (M283.006, lines
187 onward) and all later M283 rows are separate units.
