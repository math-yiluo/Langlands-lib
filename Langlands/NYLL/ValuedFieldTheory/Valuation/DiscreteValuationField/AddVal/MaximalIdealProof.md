# NYLL M311.001: maximal-ideal powers and additive valuation

This module proves the published closed proposition
`Langlands.NYLL.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_geStatement`
under the required adapted source name
`Langlands.NYLL.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_ge`.
For an arbitrary universe `u`, its unfolded type is

```lean
∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (a : R) (n : ℕ),
  a ∈ IsLocalRing.maximalIdeal R ^ n ↔
    (n : ℕ∞) ≤ _root_.IsDiscreteValuationRing.addVal R a
```

The theorem's declared result is the named proposition itself at universe `u`.
It preserves every binder and hypothesis, including explicit `a` and `n` inside
the proposition. The valuation is Mathlib's normalized additive valuation with
values in the extended natural numbers, and the ideal is the actual maximal
ideal of the given DVR.

## Implemented proof and dependencies

After introducing the ring, its three instances, the element and the exponent,
the proof applies the existing Library theorem
`_root_.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal` with
`R := R`, `n := n` and `x := a`. That theorem has the same arbitrary-universe
commutative ring, domain and DVR hypotheses; its element and exponent binders
are implicit. No further premise or instance is introduced.

The imports are the published target module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal.Statements`
and the named theorem's module
`Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth`.
The latter is already an import of the former; it is also named directly to
make the proof's mathematical dependency explicit. The published target and
its dependencies are unchanged. This module adds only the compatibility proof,
and does not use M311.002 or prove a reciprocity assertion.

## Source correspondence and attribution

The original is Naganori Yamaguchi's *ClassFieldTheory*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/AddVal.lean`,
M311.001, lines 29–33 (docstring at lines 27–28). Its whole-file SHA-256 is
`01db02718360b0849b6630cba727ac2c82a7c9e3185dc57621a85bf036c17c16`.
It is retained in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL-specific erratum was found among the current Library errata filenames.

The original theorem chooses an irreducible element, rewrites the maximal
ideal as its principal ideal, and translates divisibility by its nth power
into the additive valuation inequality. The present proof instead reuses the
published Library theorem by name. Its adaptations are the `Langlands.NYLL`
namespace prefix, the closed named-proposition result type, the focused
imports, and that proof-route replacement. The original docstring is retained;
the original theorem has no theorem attribute.

Worker 289 reused Worker 313's proof and initial documentation from Task 5884's
revision-2 draft, completed this documentation and restored the source
docstring. Worker 313 is credited as a coauthor of the contribution. The
original copyright, Apache-2.0 and author header is retained together with an
explicit modification record. Existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` apply, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The imported Library module retains its Anthropic-FLT attribution and license
files; this proof copies none of that module's implementation.
