# Successive quotients of included principal-unit subgroups

Worker 232 adapts Naganori Yamaguchi's `Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`
from `n-yamaguchi-0729/ClassFieldTheory`, commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The retained source is under `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Registered source: `nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Apache-2.0 copyright and author header is retained, with LICENSE and NOTICE in `licenses/NYLL/`.

The exact source command ranges are M144.108 lines 1997–1999, M144.110 lines 2011–2013,
M144.111 lines 2016–2022, M144.113 lines 2035–2041 and M144.117 lines 2075–2083.

| Unit | Original name in `CyclicCohomology` | Adapted name |
| --- | --- | --- |
| M144.108 | `chosenNormalBasisPrincipalUnitSuccSubgroup` | `Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSuccSubgroup` |
| M144.110 | `chosenNormalBasisPrincipalUnitSuccQuot` | `Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSuccQuot` |
| M144.111 | `chosenNormalBasisPrincipalUnitSuccQuotCommGroup` | `Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSuccQuotCommGroup` |
| M144.113 | `chosenNormalBasisPrincipalUnitSuccQuotMk` | `Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSuccQuotMk` |
| M144.117 | `chosenNormalBasisPrincipalUnitSuccQuotLift` | `Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSuccQuotLift` |

For any two actual subgroups `Vn`, `Vsucc` of `𝒪[L]ˣ` with inclusion `hV : Vsucc ≤ Vn`,
the denominator is `Vsucc.subgroupOf Vn`. The quotient is the actual group quotient of `Vn`
by this denominator. The construction includes its canonical commutative-group instance,
quotient homomorphism and the lift of a homomorphism that kills the denominator.
No normal-basis origin of the supplied subgroups is assumed. The inclusion argument in the
denominator construction is deliberately unused, exactly as in the source.

All data construction bodies, including the `change` and `infer_instance` proof terms, are
unchanged. The only changes are the `Langlands.NYLL` namespace prefix, reduced Mathlib imports,
extraction into a focused file and this modification record. The complete effective source
telescope is `(L : Type u) [Field L] [ValuativeRel L]`, followed by the displayed arguments;
`K` and the source section's other instances are absent from these definitions. The lift
retains the independent target universe of `{H : Type*}` and `[Group H]` in their source order.
The named group instance is installed only for the new opaque quotient definition, so it adds
no competing instance to an existing Mathlib type. The source calls the group a principal-unit
quotient, but this generic construction requires only the supplied inclusion of subgroups.

Mathlib's `Subgroup.subgroupOf`, `QuotientGroup.mk'`, `QuotientGroup.lift` and the canonical
commutative quotient group instance supply the constructions; there is no pre-existing
normal-basis-specific wrapper under these Lean names. This is a definition contribution.
Representative and identity criteria are separate Prop-valued statement targets; no such
target is proved here. This support contributes no host reciprocity or class-formation result.
