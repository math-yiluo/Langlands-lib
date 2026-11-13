# NYLL M311.001: maximal-ideal powers compatibility target

This module retains the required NYLL compatibility target for M311.001, lines 29–33, from Naganori Yamaguchi's *ClassFieldTheory*,
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/AddVal.lean` (whole-file SHA-256 `01db02718360b0849b6630cba727ac2c82a7c9e3185dc57621a85bf036c17c16`).
The original copyright and author header is preserved. The registered source is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
its Apache-2.0 attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL-specific erratum was found in the Library errata filenames.

## Exact proposition and source correspondence

The definition lies in `Langlands.NYLL.IsDiscreteValuationRing`. The original theorem name is
prefixed with `Langlands.NYLL` and gains the suffix `Statement`. Its full
proposition body, including every source parameter and hypothesis, is:

```lean
def mem_maximalIdeal_pow_iff_addVal_geStatement : Prop :=
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (a : R) (n : ℕ),
    a ∈ IsLocalRing.maximalIdeal R ^ n ↔
      (n : ℕ∞) ≤ _root_.IsDiscreteValuationRing.addVal R a

```

The compatibility target retains the source's unrestricted universe, commutative ring,
domain and DVR hypotheses: membership in the nth maximal-ideal power is equivalent
to normalized additive valuation at least n. The addVal constant is explicitly rooted
to prevent collision with the adapted namespace.

## Named Library reuse

The published theorem `_root_.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal`
in `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth`
already proves M311.001 with the same universe and hypotheses. It takes a and n
implicitly; specializing those binders gives the exact body above. This imported
theorem is the mathematical result to reuse. The new Prop name is retained only
because Task 5884 explicitly requires that NYLL compatibility target and a later
exact proof under `Langlands.NYLL.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_ge`.
That proof can directly apply the published theorem; the NYLL source proof is not
re-ported. A focused Lean check of the exact target using that theorem succeeds.

M311.002, `addVal_ringEquiv`, is also already covered by the same module's
`_root_.IsDiscreteValuationRing.addVal_smul`, specialized to the natural action of
`R ≃+* R` on R. The redundant M311.002 target is omitted. The M323.001 proof can
reuse `addVal_smul` directly for the published valuation-ring automorphism.
This removes M311.002 from the new prerequisite closure without dropping its
mathematical content.

## Modifications and dependency boundary

Worker 296 extracted the displayed source signatures into closed `def`s returning
`Prop`: section parameters and theorem binders now occur under `∀` inside the
proposition. The source binder kinds and parameter order are retained, as are all
independent universe levels and hypotheses. The proofs, theorem attributes and
unused surrounding declarations are omitted. The namespace gains the prefix
`Langlands.NYLL`. Source names for the two DVF namespaces are expanded to the
published qualified names; Mathlib constants keep their original meaning.

The source's whole-module imports are replaced by exactly these focused imports:

- `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth`.

This is a compatibility proposition target; this module supplies no proof of it. In
particular, it adds no premise assuming its conclusion and no global instance.
The target refers directly to Mathlib maximal ideals and normalized additive
valuation; the named imported Library theorem supplies its mathematics. Compilation and proposition inspection are development evidence only;
independent semantic acceptance and publication remain required.

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with hashes `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No feasibility proof patch or unpublished draft is reused here. The target
environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
