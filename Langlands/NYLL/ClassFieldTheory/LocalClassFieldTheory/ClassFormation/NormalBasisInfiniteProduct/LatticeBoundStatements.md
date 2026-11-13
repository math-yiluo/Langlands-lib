# NYLL lattice bounds and principal-unit convergence statements

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
| M150.001 | `chosenBaseUniformizerPow_integerRingFieldSubmodule_exists_mem_maximalIdeal_pow` | 40–59; 40–44 | `chosenBaseUniformizerPow_integerRingFieldSubmodule_exists_mem_maximalIdeal_powStatement` |
| M150.002 | `chosenNormalBasisPrincipalUnitSet_mem_principalUnits_succ_of_lattice_bound` | 63–91; 63–70 | `chosenNormalBasisPrincipalUnitSet_mem_principalUnits_succ_of_lattice_boundStatement` |
| M150.003 | `tendsto_chosenNormalBasisPrincipalUnitSequence_one_of_lattice_bound` | 95–117; 95–104 | `tendsto_chosenNormalBasisPrincipalUnitSequence_one_of_lattice_boundStatement` |

A base-uniformizer-power integer-ring lattice element is represented in the corresponding maximal-ideal power; a deep normal-basis correction lies in an ordinary principal-unit level; sequences of these corrections converge to one.

M150.001 retains the membership premise `hx` and the exact existential representative in `𝒪[L]`, its maximal-ideal-power membership and equality in `L`. M150.002 retains `hb`, `hbn` and `hz`, and the exact offsets `n + i` and `1 + i`. M150.003 retains the same bound premises and the sequence membership premise, with convergence measured after coercion to `𝒪[L]`, from `atTop` to the neighborhood filter of one.

The common source section telescope is at lines 30–34. M150.001 follows the source `omit` at line 36, removing `[FiniteDimensional K L]` and `[IsGalois K L]` while keeping the base local-field structure and valuation extension. M150.002 keeps the whole common telescope. M150.003 keeps that telescope followed by its own `[UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]`, in source order. The complete effective telescopes and explicit premises are reproduced below.

The explicit telescope of M150.001 (the concluding `Prop` body is the source target):

```lean
def chosenBaseUniformizerPow_integerRingFieldSubmodule_exists_mem_maximalIdeal_powStatement
    (K L : Type u)
    [Field K]
    [Field L]
    [Algebra K L]
    [ValuativeRel K]
    [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (m : Nat) {x : L}
    (hx : x ∈ chosenBaseUniformizerPowSubmodule K L m
      (integerRingFieldSubmodule K L))
```

The explicit telescope of M150.002 (the concluding `Prop` body is the source target):

```lean
def chosenNormalBasisPrincipalUnitSet_mem_principalUnits_succ_of_lattice_boundStatement
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
    {b n i : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b
        (chosenNormalBasisIntegerLattice K L) ≤
      integerRingFieldSubmodule K L)
    (hbn : b + 1 ≤ n) {z : 𝒪[L]ˣ}
    (hz : z ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
```

The explicit telescope of M150.003 (the concluding `Prop` body is the source target):

```lean
def tendsto_chosenNormalBasisPrincipalUnitSequence_one_of_lattice_boundStatement
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

The focused imports are the published modules:

- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U044.Definitions`
- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U059.Definitions`
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions`

They supply the actual normal-basis carriers, lattices and integer-unit operations used in these targets. No source proof needed only by the original theorem proof is imported or reproduced.

Modifications: prefix the namespace by `Langlands.NYLL`, append `Statement` to theorem names, extract this focused pair, replace broad source imports with the focused published imports, remove unused namespace openings and commands, and replace theorem proofs by their exact `Prop`-valued targets. Effective source theorem telescopes are explicit so that `def` does not drop ambient instances. Each declaration has a scoped unused-variable linter suppression to retain all named source premises and the full instance telescope even where the conclusion does not depend on them. Quantifiers, binder kinds, local instances and coercions in each target remain unchanged. No proof of any target or conflicting global instance is introduced.

The original copyright and author header is retained. The Apache-2.0 `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply. These supporting statement families do not establish a class-formation or reciprocity theorem.
