# Identity classes in an integer-unit level quotient

Worker 628 adapts Naganori Yamaguchi's M146.010,
`CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff`, from
`Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientReps.lean`,
lines 105–111, at commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`0165f6ca2068526dbcf038b890ae51cfeebdc9ed4838cb60425a458a265f3996`.

The theorem
`Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff`
has the exact target
`Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iffStatement K n x`.
It says that the canonical class of an integer unit `x` in
`IntegerUnitsModPrincipalUnitsAtLevel K n` is the identity if and only if
`x ∈ principalUnits K n`. The complete telescope retains explicit
`K : Type u`, instances `[Field K] [ValuativeRel K]`, explicit natural
level `n` and explicit integer unit `x`, in source order. All natural
levels are allowed, with no topology or local-field assumption.

The proof unfolds the target and canonical projection to
`(QuotientGroup.mk x : 𝒪[K]ˣ ⧸ principalUnits K n) = 1 ↔
x ∈ principalUnits K n`, then applies Mathlib's
`QuotientGroup.eq_one_iff`. This is the original source proof.
The only import is the published `QuotientReps.Statements` module, which
supplies the quotient and principal-unit definitions through
`QuotientReps.Definitions` and the generic quotient-group theorem through
Mathlib. No other NYLL proof is used.

The adaptation prefixes the namespace by `Langlands.NYLL`, replaces the
broad source import by the focused statement import, and states the
conclusion as the exact named Statement application. The original proof,
universe and complete telescope are preserved.
The original copyright and author header is retained; the Library's
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply under Apache-2.0.

The readable original is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the supplemental registration is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL errata note was found. This quotient-interface result
does not establish a host class-formation or reciprocity theorem.

Development check `28741708-9777-475a-a3e8-382d91dfa923` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` built this module and inspected the
complete theorem: exit code zero, no errors or warnings, universe parameter
`u`, and only `propext`, `Classical.choice`, `Quot.sound` among its axioms.
Independent review and exact-target validation remain separate requirements.
