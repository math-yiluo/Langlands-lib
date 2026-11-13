# NYLL correction-product membership and limit statements

Worker 197 adapts the units below from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisInfiniteProduct.lean`.
The readable pinned original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, and
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL errata entry was found in the Library.

| Unit | Original name in `LocalClassFieldTheory` | Source lines; target lines | Adapted name in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- | --- | --- |
| M150.013 | `chosenNormalBasisPrincipalUnitCorrectionProduct_mem` | 298–316; 298–307 | `chosenNormalBasisPrincipalUnitCorrectionProduct_memStatement` |
| M150.015 | `exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProduct_principalUnit` | 364–386; 364–377 | `exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProduct_principalUnitStatement` |
| M150.016 | `chosenNormalBasisPrincipalUnitCorrectionProduct_limit_mem` | 391–425; 391–408 | `chosenNormalBasisPrincipalUnitCorrectionProduct_limit_memStatement` |
| M150.017 | `exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProduct` | 430–473; 430–442 | `exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProductStatement` |

Finite normal-basis correction products remain in a multiplicatively closed level; under a lattice bound their products have a principal-unit limit; a unit limit remains in a closed level; every sufficiently deep sequence has a unit limit in its initial level.

M150.013 preserves the exact multiplicative-closure premise `hmul`, the sequence membership `hz`, and explicit partial-product length `d`. M150.015 preserves the lattice bound and yields a limit in the actual subgroup `principalUnits L 1`. M150.016 keeps `hclosed`, `hmul`, `hz` and the convergence hypothesis `hx`, asserting carrier membership of the supplied unit limit. M150.017 retains the high-level existential bound, sequence quantifier and conjunction of integer-ring convergence with carrier membership. All displayed unit-to-integer-ring coercions remain unchanged.

The common source section telescope is at lines 30–34. M150.013 follows the source `omit` at line 295, removing only the valuation-extension instance. M150.015 keeps the full common telescope and then the three local uniform-space instances on `L`. M150.016 follows the `omit` at line 388, removing only the valuation-extension instance, and keeps those local uniform-space instances. M150.017 keeps the full common telescope followed by those instances and `[Module.Finite 𝒪[K] 𝒪[L]]`. Source ordering and binder kinds are reproduced below.

The explicit telescope of M150.013 (the concluding `Prop` body is the source target):

```lean
def chosenNormalBasisPrincipalUnitCorrectionProduct_memStatement
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
    {n : Nat}
    (hmul : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u * v ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
    (d : Nat)
```

The explicit telescope of M150.015 (the concluding `Prop` body is the source target):

```lean
def exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProduct_principalUnitStatement
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
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    {b n : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b
        (chosenNormalBasisIntegerLattice K L) ≤
      integerRingFieldSubmodule K L)
    (hbn : b + 1 ≤ n) (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
```

The explicit telescope of M150.016 (the concluding `Prop` body is the source target):

```lean
def chosenNormalBasisPrincipalUnitCorrectionProduct_limit_memStatement
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
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    {n : Nat}
    (hclosed : IsClosed
      ((chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) : Set L)))
    (hmul : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u * v ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
    (x : 𝒪[L]ˣ)
    (hx : Tendsto
      (fun d : Nat =>
        ((chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d : 𝒪[L]ˣ) :
          𝒪[L]))
      atTop (nhds ((x : 𝒪[L]ˣ) : 𝒪[L])))
```

The explicit telescope of M150.017 (the concluding `Prop` body is the source target):

```lean
def exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProductStatement
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
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Module.Finite 𝒪[K] 𝒪[L]]
```

The focused imports are the published modules:

- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U044.Definitions`
- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U059.Definitions`
- `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct.CorrectionProduct`
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions`

They supply the actual normal-basis carriers, lattices and integer-unit operations used in these targets. No source proof needed only by the original theorem proof is imported or reproduced.

Modifications: prefix the namespace by `Langlands.NYLL`, append `Statement` to theorem names, extract this focused pair, replace broad source imports with the focused published imports, remove unused namespace openings and commands, and replace theorem proofs by their exact `Prop`-valued targets. Effective source theorem telescopes are explicit so that `def` does not drop ambient instances. Each declaration has a scoped unused-variable linter suppression to retain all named source premises and the full instance telescope even where the conclusion does not depend on them. Quantifiers, binder kinds, local instances and coercions in each target remain unchanged. No proof of any target or conflicting global instance is introduced.

The original copyright and author header is retained. The Apache-2.0 `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply. These supporting statement families do not establish a class-formation or reciprocity theorem.
