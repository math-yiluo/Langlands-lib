# NYLL M025.005: membership in the natural-multiple image

This file adapts the statement of `ClassFormation.mem_nsmulImage_iff` in
Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Valuation.lean`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, lines 62–63
(original proof at line 64; original simp attribute at line 61).
The exact source file SHA-256 is
`f630b84345567adaa22a76feb4a0c2716079721e29a7d3b12bf5c6bd52cabb0c`.
The file is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered source collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the supplemental registration is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The original declaration
`ClassFormation.mem_nsmulImage_iff` (M025.005) corresponds to
`Langlands.NYLL.ClassFormation.mem_nsmulImage_iffStatement`.
It is a proposition-valued `def` with complete explicit telescope
`(Z : AddSubgroup ZHat) (n : ℕ) (z : ZHat)`. It has no implicit,
typeclass or universe parameters and no omitted hypotheses. Its body is
exactly the source proposition, with the namespace-adapted `ZHat` and
`nsmulImage`:

```lean
z ∈ nsmulImage Z n ↔ ∃ x ∈ Z, n • x = z
```

Thus an ambient profinite integer lies in the natural-multiple image of
`Z` if and only if it is `n` times an element of `Z`. This includes `n = 0`.
It uses the actual ambient image `nsmulImage`, rather than the subgroup
`nsmulWithin` whose ambient type is `Z`.

Worker 192 made these modifications: extract this one theorem's statement;
prefix the namespace by `Langlands.NYLL`; change `theorem` to `def` returning
`Prop`, append `Statement`, and omit the proof and `@[simp]` attribute.
The unused source namespace opens, `noncomputable section`, universe and
group/typeclass section variables are omitted; none contributes a parameter
to this source statement. The full degree/norm imports are replaced by
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.Definitions`,
which supplies the exact adapted data, and its transitive published
profinite-integer and Mathlib infrastructure. No other modification is made.

Mathlib's `AddSubgroup.mem_map` is the generic membership fact for subgroup
images; the present contribution records the exact named NYLL specialization
requested by the source inventory. It does not publish a proof or add a simp
rule. Proof of this target is separate work after statement publication.
No new instance, quotient comparison or local reciprocity result is asserted.

The Lean file retains the original copyright and author header.
The retained Apache-2.0 license and notice are `licenses/NYLL/LICENSE`
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE`
(SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
