# Actual integral-closure standard complete-DVF existence

The theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_completeDVF.{u,v,w}`
proves exactly the published closed proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.ExistsIntegralClosureStandardCompleteDVFStatement.{u,v,w}`.
Its entire unapplied type is that named proposition. Only the independent
universe levels `u`, `v`, and `w` parameterize the declaration.

Inside the proposition the quantifiers are, in order, `K : Type u`,
`L : Type w`, `[Field K]`, `[Field L]`, the supplied `[Algebra K L]`,
`[FiniteDimensional K L]`,
`base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u,v} K`,
and `[Algebra.IsSeparable K L]`. The supplied algebra is arbitrary. The
identity extension is included. No additional mathematical premise is added.

Writing `A := base.valuation.valuationSubring` and `B := integralClosure A L`,
the conclusion is exactly

```lean
∃ target : CompleteDVF.{w, 0} L,
  (∀ z : L,
    z ∈ target.valuation.valuationSubring ↔ z ∈ B.toSubring) ∧
  ∃ _ : B ≃+* target.valuation.valuationSubring, True
```

The algebra structure from `A` to `L` is induced by the inclusion `A → K`
and the supplied `algebraMap K L`. Thus `B` is the actual subalgebra of this
same `L` consisting of elements integral over `A`. The first conjunct compares
membership in `L`; the second provides a ring equivalence for the same target.
The target's value-group universe is `0`, independently of all three input
universes. The chosen value group is `WithZero (Multiplicative ℤ)`.

## Implemented proof

1. Apply the published finite-separable localness and DVR theorems to `K`, `L`,
   and `base`, installing their conclusions only locally for `B`. Mathlib
   provides its domain structure and the fraction-ring structure
   `IsFractionRing B L` through
   `integralClosure.isFractionRing_of_finite_extension K L`.
2. Set `vL := (IsDiscreteValuationRing.maximalIdeal B).valuation L`.
   Mathlib's `IsDiscreteValuationRing.equivValuationSubring` gives
   `e : B ≃+* vL.valuationSubring`, and its `isRankOneDiscrete` instance gives
   discreteness of this standard valuation.
3. Give `vL.valuationSubring` its local `B`-algebra structure through `e`.
   The same equivalence becomes a `B`-linear equivalence `eLin` by
   multiplicativity. The published M245.014 theorem gives completeness of
   `B` for `CanonicalIntegralClosure.maximalIdeal base`; unfolding that name
   identifies it with `IsLocalRing.maximalIdeal B`, using the published
   localness witness. Apply the universe-general published
   `isAdicComplete_of_linearEquiv.{w,w,w}` to `B`, `B`, and
   `vL.valuationSubring` to transport completeness for this ideal.
4. Apply `IsAdicComplete.map_algebraMap_iff` to express completeness for the
   mapped ideal in `vL.valuationSubring`. An element of a local ring belongs
   to its maximal ideal exactly when it is a nonunit. Since `e` and its
   inverse preserve units, an element of `B` belongs to its maximal ideal
   exactly when its image belongs to the maximal ideal upstairs.
   Surjectivity of `e` then proves that the mapped maximal ideal is exactly
   `IsLocalRing.maximalIdeal vL.valuationSubring`. Rewriting yields the
   completeness field required by `Valuation.IsCompleteDiscrete vL`.
5. Mathlib's `IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring`
   identifies the image of the whole ring `B` in `L` with the standard
   valuation subring. In one direction, unpack an image witness `b : B`;
   its subtype proof gives integral-closure membership. In the other, use
   `⟨z, hz⟩ : B` as the image witness. This proves the pointwise membership
   equivalence for every `z : L`.
6. Package `vL` and its proved completeness as a single
   `target : CompleteDVF.{w,0} L`. Supply the membership equivalence and `e`
   for this very target, finishing with `True.intro`.

The proof imports the unchanged published statement and preserves its import
closure. The localness, DVR and completeness facts are proved results, not
extra hypotheses. All introduced algebra and completeness instances are local
to the proof. Chosen extension packages, `HasExtension`, fundamental identities,
uniqueness and host reciprocity remain separate obligations.

## Source correspondence

The source is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean)
at commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. Its SHA-256 is
`43c21425b2c39e7e6e5d2bca1f2b615c5c29e9d91e69d32d079e593df3170094`.
The full M245.017 assertion and proof at lines 513–629 and ambient context
at lines 1–64 and 508–633 were read, including universes at line 23 and
field/algebra/finite-dimensional variables at lines 30–31.

| Original declaration or API | Adapted declaration or API |
| --- | --- |
| `ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_completeDVF`, M245.017 | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_completeDVF.{u,v,w}` |
| M245.006 `integralClosure_isLocalRing_of_finite_separable` | Published theorem with the same suffix in `Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension` |
| M245.011 `integralClosure_isDiscreteValuationRing_of_finite_separable` | Published theorem with the same suffix in that namespace |
| M245.014 `integralClosure_maximalIdeal_isAdicComplete_of_finite_separable` | Published theorem with the same suffix, whose target uses `CanonicalIntegralClosure.maximalIdeal` |
| M105.001 `isAdicComplete_of_linearEquiv` | Published universe-general closed theorem in `Langlands.NYLL.ValuationTheory.DiscreteValuationField`, imported from `HenselianFinite.CompletenessProofs` |
| `isAdicComplete_map_algebraMap_iff` | Current Mathlib `IsAdicComplete.map_algebraMap_iff` |

The source theorem's ambient mathematical variables become internal binders
of the closed proof target. The original proof route, standard valuation,
ring equivalence, maximal-ideal image argument and pointwise comparison are
retained. Calls to the four published closed theorems explicitly supply their
type parameters; the canonical maximal-ideal name is unfolded at the
completeness step. The source abbreviation `base.valuationSubring` is expanded
to `base.valuation.valuationSubring`, and the adic-completeness API spelling is
updated, with its module argument supplied explicitly. Focused imports replace the source's larger `FiniteExtension.Core`
closure. The intervening source M245.015/.016 wrappers are not used.

The registered source snapshot is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The registered attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was found in the checked workspace, project or Library
notes on 31 October 2026. M245 has no recorded patch10 compatibility change;
no implementation from that patch is reused here.

## Attribution and modifications

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi (`https://github.com/n-yamaguchi-0729`), all rights
reserved; authors Naganori Yamaguchi (assisted by OpenAI Codex). The license
is Apache-2.0. Unmodified copies of its
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain in `licenses/NYLL/`.
The selected source has no source-specific NOTICE entry; the retained credits
remain applicable.

Worker 384 extracted and adapted this proof, added the `Langlands.NYLL`
namespace prefix and exact closed target binding, made the published theorem
applications explicit, expanded the valuation-subring abbreviation, matched
the canonical maximal ideal, updated the Mathlib API spelling and imports,
and wrote this Markdown on 31 October 2026. No implementation draft was
supplied by another project worker. Public theorem imports are reused by
Lean name.

The source uses Lean 4.35.0-rc2 / Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The adaptation uses approved
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 / Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
