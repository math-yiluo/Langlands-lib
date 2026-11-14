# NYLL transfer norm double-coset identity target

Worker 196, 14 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Registered source
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright and author header is retained; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

Source module:
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainTransfer.lean`.

| Unit | Original declaration | Adapted declaration | Source lines |
| --- | --- | --- | --- |
| M071.024 | `ClassFormation.transferNormNaturality_norm_doubleCoset_formula` | `Langlands.NYLL.ClassFormation.transferNormNaturality_norm_doubleCoset_formulaStatement` | theorem type 722–740 |

## Statement

For an integral representation `A`, closed subgroups `L ≤ K' ≤ K`, normality
of `L` inside `K`, finiteness of `K/L`, and `a` in the actual fixed additive
subgroup `A_L`, the following elements of `A_K'` agree: the inclusion of
`relativeNorm A K L (hLK'.trans hK'K) a`, and the `L | K'` relative norm of
`transferNormNaturalityNormWitness A K K' L hLK' hK'K a`. The witness is the
published sum of quotient-action translates indexed by the chosen right
transversal. The equality keeps its source orientation.

The ordered telescope preserves implicit `G`, its `Group` and
`TopologicalSpace` instances, explicit `A`, `K K' L`, `hLK'`, `hK'K`,
the named normality instance `hLnormal`, the finite quotient instance, and
explicit `a`. The operative source `Representation` section at
`MainTransfer.lean:620–623` already declares `G : IntegralRepGroupType`.
The source alias is defined as `Type 0` at
`Nyll/GaloisCohomology/Cyclic/IntegralRepUniverse.lean:18`; the published
alias and this universe-zero scope are retained unchanged.
There is no finiteness assumption on `G` itself and no extra normality,
intermediate-quotient finiteness, or norm-identity hypothesis.

Two local instances inside the proposition are retained verbatim up to the
name and subgroup adaptations: normality of `L` in `K'` is obtained from the
published M068.003 theorem
`Langlands.NYLL.ClassFormation.transferNormNaturality_intermediateExtension_normal`;
finiteness of `K'/L` is obtained by `Finite.of_injective` applied to the
actual intermediate inclusion and the published M071.003 theorem
`Langlands.NYLL.ClassFormation.transferNormNaturalityIntermediateInclusion_injective`.
These are the original proof terms in the original order. No global
instance is introduced.

## Modifications and dependencies

Prefix the namespace with `Langlands.NYLL`, append `Statement`, and replace
the theorem by a Prop-valued `def` containing its entire original type.
The original theorem proof beginning at line 740 is omitted. Replace broad
source imports with the five focused imports in the Lean file. They supply
published M071.022, M024.009, M028.001, M071.003 and M068.003, respectively,
rather than assumptions or inline substitute proofs. M028.001 supplies the
actual fixed-field inclusion.

Expand `CyclicCohomology.extensionSubgroup K L hLK` to
`L.toSubgroup.subgroupOf K.toSubgroup`, its exact body at
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean:51–54`.
Keep all containment witnesses even where the expansion makes one unused.
All maps, coercions, argument order, and local-instance terms remain as in
the source. The noncomputable section and source attribution remain.
The comment introducing the group binder describes the retained source
alias directly. The source's accompanying comment attributes this scope
to Mathlib's `Rep`; that attribution does not apply to the pinned
Mathlib `RepresentationTheory/Rep/Basic.lean:24–37`, where coefficient,
group and representation-carrier universes are independent.

## Validation and scope

Development check `bf1ee10b-991c-4bc0-bf50-81aaad1aa2d4`, in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, compiled the statement and the
source comparison without errors or warnings. The private comparison reconstructs the complete unapplied source statement
constant with the original `extensionSubgroup` abbreviation and compares it
with this constant by reflexivity. Exact declaration inspection
`9db355d0-1824-4bfd-8b80-6b8803e8bd3f` confirms that this target returns
`Prop`, has no universe parameters, and compiles without errors or warnings. These development checks supply
neither a proof of this equality nor independent semantic acceptance.
After the provenance correction, development inspection
`13946e6d-8687-4d0e-8dc1-c9fe520c5aae` again confirms `Prop`, no universe
parameters, and zero errors or warnings; the proposition is unchanged.
The proof of M071.024 is separate `lean.proof@1` work. This target adds no
host reciprocity comparison or completion claim for the whole port.
