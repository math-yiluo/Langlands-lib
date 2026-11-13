# NYLL one-step norm and coboundary lifting statements

Worker 197 adapts the units below from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGradedLifting.lean`.
The readable pinned original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, and
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL errata entry was found in the Library.

| Unit | Original name in `LocalClassFieldTheory` | Source lines; target lines | Adapted name in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- | --- | --- |
| M154.005 | `exists_chosenNormalBasisPrincipalUnit_h0_oneStep_lifting` | 163–308; 163–174 | `exists_chosenNormalBasisPrincipalUnit_h0_oneStep_liftingStatement` |
| M154.006 | `exists_chosenNormalBasisPrincipalUnit_hMinusOne_oneStep_lifting` | 313–483; 313–326 | `exists_chosenNormalBasisPrincipalUnit_hMinusOne_oneStep_liftingStatement` |

Sufficiently deep fixed units are a same-level Tate norm times a fixed unit one level deeper; for a chosen Galois generator, sufficiently deep norm-one units are a same-level coboundary times a norm-one unit one level deeper.

Both targets retain the source local `letI` installing the actual integer-unit Galois action. M154.005 retains the high-level existential bound, the fixed-unit premise, the same-level factor `b`, the successor-level fixed factor `a'` and the exact Tate-norm factorization. M154.006 retains the generator hypothesis, the norm-one premise and successor-level norm-one condition, and the exact multiplicative-coboundary factorization.

The common source section telescope is at lines 30–35, followed in each theorem by its own topology, local-field and finite-generation instances on the extension. The second theorem also retains the explicit automorphism `g` and generator hypothesis `hgen`. No ambient instance or source hypothesis is omitted; complete effective telescopes appear below.

The explicit telescope of M154.005 (the concluding `Prop` body is the source target):

```lean
def exists_chosenNormalBasisPrincipalUnit_h0_oneStep_liftingStatement
    (K L : Type u)
    [Field K]
    [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]
    [ValuativeRel K]
    [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Module.Finite 𝒪[K] 𝒪[L]]
```

The explicit telescope of M154.006 (the concluding `Prop` body is the source target):

```lean
def exists_chosenNormalBasisPrincipalUnit_hMinusOne_oneStep_liftingStatement
    (K L : Type u)
    [Field K]
    [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]
    [ValuativeRel K]
    [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    (g : Gal(L/K)) (hgen : ∀ sigma : Gal(L/K),
      sigma ∈ Subgroup.zpowers g)
```

The focused imports are the published modules:

- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U059.Definitions`
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.IntegerDefinitions`
- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Definitions`

They supply the actual normal-basis carriers, lattices and integer-unit operations used in these targets. No source proof needed only by the original theorem proof is imported or reproduced.

Modifications: prefix the namespace by `Langlands.NYLL`, append `Statement` to theorem names, extract this focused pair, replace broad source imports with the focused published imports, remove unused namespace openings and commands, and replace theorem proofs by their exact `Prop`-valued targets. Effective source theorem telescopes are explicit so that `def` does not drop ambient instances. Each declaration has a scoped unused-variable linter suppression to retain all named source premises and the full instance telescope even where the conclusion does not depend on them. Quantifiers, binder kinds, local instances and coercions in each target remain unchanged. No proof of any target or conflicting global instance is introduced.

The original copyright and author header is retained. The Apache-2.0 `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply. These supporting statement families do not establish a class-formation or reciprocity theorem.
