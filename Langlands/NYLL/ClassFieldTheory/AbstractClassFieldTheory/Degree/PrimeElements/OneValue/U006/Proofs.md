# NYLL M028.006: coercion of the value one

The paired Lean file proves exactly
`Langlands.NYLL.ClassFormation.ValuationData.oneValue_coeStatement v`
under the required name
`Langlands.NYLL.ClassFormation.ValuationData.oneValue_coe`.
It imports the published statement module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.OneValue.Statements`.
No existing definition or statement is changed.

The complete telescope retains implicit `G : IntegralRepGroupType`,
`[Group G]`, `[TopologicalSpace G]`, implicit `D : DegreeData G`,
implicit `A : Rep ℤ G`, and explicit `v : ValuationData D A`.
The group is in universe zero; the representation carrier has one arbitrary
universe parameter.

## Implemented proof

The proof is `rfl`, exactly as in the source. Unfolding the proposition and
`ValuationData.oneValue` reduces the coerced subtype element to
`(1 : Langlands.NYLL.ClassFormation.ZHat)`. The membership certificate
in the subtype construction imposes no extra hypothesis.

The only direct import is the published statement module, whose dependencies
supply the actual valuation data, value group and distinguished element.
No private lemma, instance, extra hypothesis or duplicate definition is added.

## Source correspondence and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean`,
M028.006: docstring at line 115, attribute at line 116, complete theorem at
lines 117–119. The surrounding section parameters are at lines 25–28.
The file SHA-256 is
`9b2f91f76898d32b4f6f556a6b628aa0c4cf40768f43423b15e81de22fadc4bf`.
The readable source is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

It belongs to registered source `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

Worker 290 prefixed the namespace with `Langlands.NYLL`, changed the
written theorem type to its exact published proposition, reduced the import,
rewrote the docstring, and omitted unused namespace openings and the source
`@[simp]` attribute. The named proposition would not serve as the original
equality simp rule without a wrapper. The source proof and binder kinds and
order are unchanged. The public port inventory records no patch10 change
for this source module.

## Attribution and scope

The original copyright, Apache-2.0 release and author header are retained.
The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply,
with respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
This support equality discharges no host class-formation, cup, transfer,
Tate or reciprocity target.
