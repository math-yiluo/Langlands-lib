# NYLL M110.014: containment in every extending valuation ring

This file proves the exact published target
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtensionStatement`
under the required source-adapted theorem name, obtained by removing
`Statement` from that name.

For fields `K` and `L` with an arbitrary `K`-algebra structure, valuations `vK`
and `vL` in independent ordered value groups, and `[vK.HasExtension vL]`,
the valuation subring constructed from the actual integral closure of
`vK.valuationSubring` in `L` is contained in `vL.valuationSubring`. The
construction requires the explicit hypothesis `hval` that every element or
its inverse belongs to that integral closure. The theorem retains that
hypothesis and the source's universes and binder order. No finite extension,
discreteness, completeness or Henselian hypothesis is added.

The proof takes an element of the constructed subring. By unfolding the
published construction `integralClosureValuationSubringOfMemOrInv` and
Mathlib's `ValuationSubring.ofSubring`, this membership is definitionally a
proof that the element is integral over `vK.valuationSubring`.
`IsIntegral.tower_top` transfers this integrality to `vL.valuationSubring`,
using the algebra and scalar tower supplied by `Valuation.HasExtension`.
Finally `Valuation.Integers.mem_of_integral`, applied to
`Valuation.valuationSubring.integers`, places the element in the target ring.

The imports are the unchanged published
`IntegralClosureValuationSubringStatements` module and
`Mathlib.RingTheory.Valuation.Integral`. The former imports the construction
and Mathlib's valuation-extension and integral-closure APIs. The proof uses
no unpublished NYLL theorem. Upstream M110.014 calls the membership lemma
M110.010 and containment lemma M110.007; here their two elementary steps are
performed directly inside this proof, as permitted by the task. No duplicate
public helper declaration, new instance or axiom is introduced, and no
published statement or dependency is modified. Worker 194 contributed guidance
on this direct proof route.

The pinned source is Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean`,
lines 314–331 (declaration), with section context at lines 21–33.
The source name
`ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension`
is prefixed by `Langlands.NYLL`. The direct integrality argument is the
source's M110.007 proof at lines 170–180.

The readable original is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean`,
SHA-256 `8f2d21dcbef11b6354d840a350ea2ddf775b670d74581bf9469d499afbe34dad`.
It belongs to registered source `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`,
also recorded by `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

The Lean file preserves the original copyright, author and Apache-2.0 header,
and records the namespace, import and proof changes by Worker 199 on
13 November 2026. The retained license and notices are
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`, with SHA-256 respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The checking environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).
