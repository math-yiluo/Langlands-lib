# Representative criteria for successive principal-unit quotients

This file adapts NYLL `Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The retained source root is `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Original copyright and author attribution remain in the Lean header; Apache-2.0 LICENSE and NOTICE
remain in `licenses/NYLL/`. Adaptation: Worker 232.

| Unit | Exact source lines | Source name in `CyclicCohomology` | Adapted name in `Langlands.NYLL.CyclicCohomology` |
| --- | --- | --- | --- |
| M144.109 | 2002–2007 | `mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iff` | `mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iffStatement` |
| M144.115 | 2052–2058 | `chosenNormalBasisPrincipalUnitSuccQuotMk_surjective` | `chosenNormalBasisPrincipalUnitSuccQuotMk_surjectiveStatement` |
| M144.119 | 2096–2104 | `chosenNormalBasisPrincipalUnitSuccQuotMk_eq_one_iff` | `chosenNormalBasisPrincipalUnitSuccQuotMk_eq_one_iffStatement` |

The targets respectively assert that membership in the denominator subgroup means membership
of the underlying unit in `Vsucc`, that the canonical quotient homomorphism is surjective, and
that a representative has quotient class one exactly when its underlying unit lies in `Vsucc`.
They apply to any actual included subgroups `Vsucc ≤ Vn` of `𝒪[L]ˣ`, without assuming a
normal-basis construction. The effective source telescope is `(L : Type u) [Field L]
[ValuativeRel L]`, then `{Vn Vsucc : Subgroup 𝒪[L]ˣ}`, `(hV : Vsucc ≤ Vn)`, and `(u : Vn)`
where present, with source binder kinds and order preserved.

Modifications: prepend `Langlands.NYLL` to the namespace, import the focused published data
module, extract these three related lemmas, and replace each theorem with a Prop-valued `def`
whose name ends in `Statement`. Each body is exactly the original theorem proposition, with
source hypotheses and quotient objects unchanged. The theorem proofs and theorem attributes
are omitted. The targets are not proofs. Mathlib's generic quotient results underlie the source
proofs but do not replace these exact source-specific target names. No host reciprocity or
class-formation conclusion is claimed.
