# Evaluation of a homomorphism lifted from an integer-unit level quotient

Worker 628 adapts Naganori Yamaguchi's M146.009,
`CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelLift_mk`, from
`Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientReps.lean`,
lines 95–103, at commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`0165f6ca2068526dbcf038b890ae51cfeebdc9ed4838cb60425a458a265f3996`.

The theorem
`Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelLift_mk`
has the exact target
`Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelLift_mkStatement n f h x`.
For any valued field `K : Type u`, group `M : Type*`, natural level `n`,
homomorphism `f : 𝒪[K]ˣ →* M` and inclusion
`h : principalUnits K n ≤ f.ker`, the descended homomorphism evaluated at
the canonical class of `x` equals `f x`. The field and target group are
implicit and may have independent universes. The explicit arguments are
`n`, `f`, `h`, `x` in source order. No topology or local-field hypothesis
is required.

The implemented proof is the source's `rfl`: the Statement unfolds to
the evaluation identity, the named lift unfolds to `QuotientGroup.lift`,
and the canonical class unfolds to `QuotientGroup.mk'`. Evaluation on that
representative reduces definitionally to `f x`.
The only import is the published `QuotientReps.Statements` module, which
imports `QuotientReps.Definitions` for these constructions and Mathlib's
quotient-group implementation. No other NYLL proof is used.

The adaptation prefixes the namespace by `Langlands.NYLL`, replaces the
broad source import by the focused statement import, and states the result
as the exact named Statement application. It preserves the original
`[simp]` attribute, proof, universes and complete telescope.
The original copyright and author header is retained; the Library's
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply under Apache-2.0.

The readable original is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the supplemental registration is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL errata note was found. This quotient-interface identity
does not establish a host class-formation or reciprocity theorem.

Development check `1eed1412-5474-4143-a0b9-59b25a3d2e5b` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` built this module and inspected the
complete theorem: exit code zero, no errors or warnings, independent universe
parameters `u` and `u_1`, and only `propext`, `Classical.choice`, `Quot.sound`
among its axioms. Independent review and exact-target validation remain
separate requirements.
