# Surjectivity from a principal-unit quotient to a larger subgroup quotient

Worker 628 adapts Naganori Yamaguchi's M148.003,
`LocalClassFieldTheory.integerUnitsModPrincipalUnitsToSubgroupQuotient_surjective`,
from
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisFiniteQuotient.lean`,
lines 70–80, at commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`e1dd0a3fafabc85f606f3441e8154d3bd597a0cef23dd33200708a4cc79cc476`.

The theorem
`Langlands.NYLL.LocalClassFieldTheory.integerUnitsModPrincipalUnitsToSubgroupQuotient_surjective`
proves the exact published
`Langlands.NYLL.LocalClassFieldTheory.integerUnitsModPrincipalUnitsToSubgroupQuotient_surjectiveStatement L m V h`.
For `L : Type u` with `[Field L] [ValuativeRel L]`, any natural level
`m`, subgroup `V : Subgroup 𝒪[L]ˣ` and inclusion
`h : principalUnits L m ≤ V`, the actual canonical homomorphism from
`IntegerUnitsModPrincipalUnitsAtLevel L m` onto `𝒪[L]ˣ ⧸ V`
is surjective. The telescope retains the source's explicit field, instances,
level, subgroup and inclusion, in that order. The original explicitly
omits topology and local-field assumptions for this theorem; none are added.
Unused source section variables concerning `K` are absent from its effective
theorem telescope and from this adaptation.

The implemented proof follows the source. Given a target quotient class,
`Quotient.inductionOn'` reduces to a representative `a : 𝒪[L]ˣ`.
Its canonical class `integerUnitsModPrincipalUnitsAtLevelMk L m a`
is a preimage. The required equality is `rfl`, because the subgroup quotient
map is the quotient lift of `QuotientGroup.mk' V`, whose evaluation on a
canonical representative reduces definitionally.
The only import is the published `SubgroupQuotientMapStatement` module.
It supplies `SubgroupQuotientMap`, the integer-unit quotient definitions and
Mathlib's quotient implementation transitively. The proof uses no M146
theorem and no unpublished result.

The adaptation prefixes the namespace by `Langlands.NYLL`, replaces the
broad source imports by the focused statement import, explicitly binds the
source's effective section parameters, and states the conclusion as the
exact named Statement application. The original proof and universe are
preserved. Unrelated namespace openings are omitted.
The original copyright and author header is retained; the Library's
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply under Apache-2.0.

The readable original is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the supplemental registration is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL errata note was found. This support result does not
establish finiteness, a host class formation or a reciprocity theorem.

Development check `b6175f19-2e1a-4f5a-a3fa-2dbc196330cc` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` built this module and inspected the
complete theorem: exit code zero, no errors or warnings, universe parameter
`u`, and only `propext`, `Classical.choice`, `Quot.sound` among its axioms.
Independent review and exact-target validation remain separate requirements.
