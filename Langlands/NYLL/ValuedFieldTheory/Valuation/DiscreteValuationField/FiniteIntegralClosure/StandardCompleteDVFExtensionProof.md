# Complete-DVF extension with its actual integral closure: proof

The theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_completeDVF_extension.{u,v,w}`
proves exactly the published closed proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.ExistsIntegralClosureStandardCompleteDVFExtensionStatement.{u,v,w}`.
Its entire unapplied type is that named proposition. Its only declaration
parameters are the independent universe levels `u`, `v` and `w`.

Inside the proposition the quantifiers are, in order, `K : Type u`,
`L : Type w`, `[Field K]`, `[Field L]`, the supplied `[Algebra K L]`,
`[FiniteDimensional K L]`,
`base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u,v} K`,
and `[Algebra.IsSeparable K L]`. The supplied algebra and base are arbitrary.
The identity extension `L = K` is included. No mathematical premise is added.

The conclusion is exactly

```lean
∃ target : CompleteDVF.{w, 0} L,
  ∃ hExt : _root_.Valuation.HasExtension base.valuation target.valuation,
    letI : _root_.Valuation.HasExtension base.valuation target.valuation := hExt
    IsIntegralClosure target.valuation.valuationSubring
      base.valuation.valuationSubring L
```

Write `A := base.valuation.valuationSubring` and
`B := target.valuation.valuationSubring`. The witness `target` has field
carrier this same `L` and value group in `Type 0`. Both `hExt` and the
integral-closure property refer to that one target. `hExt` is Mathlib's
actual `Valuation.HasExtension` along the supplied `algebraMap K L`. The
algebra `A → L` is the inclusion `A → K` followed by `algebraMap K L`. The
algebra `B → L` is the inclusion of the valuation subring. The
`IsIntegralClosure B A L` conclusion uses these two maps. It says that
`B → L` is injective. It also says that each `z : L` is integral over `A`
exactly when `z` is the image of some element of `B`.

## Implemented proof

1. Introduce `K`, `L`, their instances and `base`. Apply the published M245.017
   theorem
   `exists_integralClosure_standard_completeDVF.{u,v,w} K L base`. It supplies
   one `target : CompleteDVF.{w,0} L` and the pointwise equivalence
   `hmem z : z ∈ B ↔ z ∈ (integralClosure A L).toSubring` for every
   `z : L`. Its ring-equivalence conjunct is not used.
2. Contraction along `K → L`. For `a : K`, prove
   `algebraMap K L a ∈ (integralClosure A L).toSubring ↔ a ∈ A`.
   Membership in the integral closure is by definition
   `IsIntegral A (algebraMap K L a)`. Mathlib's `isIntegral_algebraMap_iff`
   rewrites this as `IsIntegral A a`. That rewrite uses the tower `A → K → L`
   and faithfulness of the field algebra `K → L`. A valuation subring is
   integrally closed (Mathlib instance in
   `Mathlib.RingTheory.Valuation.LocalSubring`). `K` is its fraction field. So
   `IsIntegrallyClosed.isIntegral_iff` turns `IsIntegral A a` into
   `∃ b : A, algebraMap A K b = a`, which is equivalent to `a ∈ A`.
3. `HasExtension`. Apply Mathlib's
   `Valuation.HasExtension.ofComapInteger`. Its hypothesis states that the
   comap of `target.valuation.integer` along `algebraMap K L` is
   `base.valuation.integer`. By extensionality, it reduces to
   `algebraMap K L a ∈ B ↔ a ∈ A` for each `a : K`. Rewriting with `hmem`
   turns this into the contraction of step 2. This gives `hExt`.
4. Supply `target` and `hExt`. Then install exactly `hExt` locally (Lean's
   `let`, matching the statement's `letI`). Build `IsIntegralClosure B A L`
   from its two fields:
   - injectivity of `algebraMap B L`, which is the subtype inclusion, by
     `Subtype.ext`;
   - for `z : L`, if `z` is integral over `A`, then `z` lies in
     `integralClosure A L`. So `hmem z` gives `z ∈ B`, and `⟨z, _⟩ : B` maps
     to `z`. Conversely, an element `y : B` satisfies
     `(y : L) ∈ integralClosure A L` by `hmem`, so its image is integral over
     `A`.

The proof imports the unchanged published statement. It does not change the
statement's import closure. The completeness, discreteness and pointwise
comparison come from the proved M245.017 theorem; they are not hypotheses.
The `HasExtension` witness and the integral-closure property are derived. A
private check confirmed three facts. The declaration's type is
syntactically the constant
`ExistsIntegralClosureStandardCompleteDVFExtensionStatement.{u,v,w}`. Its
level parameters are `[u, v, w]`. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

This theorem does not cover the following, which remain separate units:
chosen local-extension data, uniqueness of the extension, the
fundamental identity `e * f = [L : K]`, finite integer-module comparisons,
inertia and host reciprocity.

## Source correspondence

The source is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean)
at commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. Its SHA-256 is
`43c21425b2c39e7e6e5d2bca1f2b615c5c29e9d91e69d32d079e593df3170094`.
The M245.018 theorem `exists_integralClosure_standard_fundamental_identity`
occupies lines 631–685, with universes at line 23 and field, algebra and
finite-dimensional variables at lines 30–31. Lines 645–674 obtain the
target, prove `HasExtension` and prove `IsIntegralClosure`; this proof
adapts them. Lines 675–685 prove only the fundamental-identity conjunct,
which the target omits; they are not adapted.

The contraction helper is
`ValuationTheory.DiscreteValuationField.Valuation.algebraMap_mem_integralClosure_valuationSubring_iff`
in
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean),
lines 190–213, at the same commit. Its SHA-256 is
`8f2d21dcbef11b6354d840a350ea2ddf775b670d74581bf9469d499afbe34dad`. On
31 October 2026, searches of the current Library and staging found no
published equivalent. It is not ported as a separate declaration. Step 2
proves the needed instance inside the proof from current Mathlib lemmas.

The downstream source consumer is M248.005,
`chosenLocalExtensionCompleteDVF_exists` in
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean`,
lines 114–128 (SHA-256
`f9f4741aa6a1584e125f571e6095b641f13f0983ccbda6225d9324b9fdc1f27c`). It
discards the fundamental identity and uses only the conclusion proved here.

| Original declaration or API | Adapted declaration or API |
| --- | --- |
| `ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_fundamental_identity`, M245.018 (existence, `HasExtension` and `IsIntegralClosure` part) | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_completeDVF_extension.{u,v,w}` |
| M245.017 `exists_integralClosure_standard_completeDVF` | Published `Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_completeDVF.{u,v,w}`, applied explicitly to `K L base` |
| `algebraMap_mem_integralClosure_valuationSubring_iff` (ChevalleyExtension.lean 190–213) | Local `have hcontract`, proved by Mathlib `isIntegral_algebraMap_iff` and `IsIntegrallyClosed.isIntegral_iff` |
| `base.valuation.HasExtension target.valuation`, `Valuation.HasExtension.ofComapInteger` | `_root_.Valuation.HasExtension base.valuation target.valuation`, the same Mathlib `_root_.Valuation.HasExtension.ofComapInteger` |
| `target.valuationSubring`, `base.valuationSubring` | Expanded to `target.valuation.valuationSubring`, `base.valuation.valuationSubring` |

Other modifications are as follows. The source's ambient mathematical
variables become internal binders of the closed target, and the ambient
universes become the declaration's level parameters. The source contraction
used `isIntegral_algHom_iff` with `IsIntegrallyClosedIn.algebraMap_eq_of_integral`;
the adaptation uses Mathlib's `isIntegral_algebraMap_iff` and
`IsIntegrallyClosed.isIntegral_iff` instead. The source installs `hExt` with
`let`, then builds and returns the integral-closure property for its
conjunction. The adaptation builds that property directly as the remaining
goal. The scalar-tower construction and `isDefectless_of_isIntegralClosure`
step at lines 675–685 are omitted. Focused imports replace the source
imports. These are the published statement and M245.017 proof modules and
`Mathlib.RingTheory.Valuation.LocalSubring`.

The registered source snapshot is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The registered attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
On 31 October 2026, the workspace, project and Library notes contained no
applicable erratum. The published partition records M245 as
`none in patch10`, and this proof reuses nothing from that patch.

## Attribution and modifications

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi (`https://github.com/n-yamaguchi-0729`), all rights
reserved; authors Naganori Yamaguchi (assisted by OpenAI Codex). The license
is Apache-2.0. Unmodified copies of its
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain in `licenses/NYLL/`.
The selected source has no source-specific NOTICE entry; the retained credits
remain applicable.

On 31 October 2026, Worker 785 did the following:
- selected and adapted this proof;
- added the `Langlands.NYLL` namespace prefix and bound the proof to the
  exact closed target;
- obtained the witness from the published M245.017 theorem;
- replaced the contraction helper by a local Mathlib-based proof;
- expanded the valuation-subring abbreviations, qualified `HasExtension` and
  focused the imports;
- wrote this Markdown.

No implementation draft from another project worker was reused. Worker 384
authored the published target statement and M245.017 proof, which are
imported by Lean name.

The source uses Lean 4.35.0-rc2 / Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The adaptation uses approved
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 / Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
