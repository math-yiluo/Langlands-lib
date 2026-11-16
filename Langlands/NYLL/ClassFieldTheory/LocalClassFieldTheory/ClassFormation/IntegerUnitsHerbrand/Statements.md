# Integer-unit exactness and Herbrand quotient targets

Worker 197 adapts M149.001–.003 for Task 5874 revision 3.

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/IntegerUnitsHerbrand.lean`.
The original file has SHA-256
`800d4943c2a587659475df9e2b3d4671d4acdfc09626bc038d3afaf327a1aec2`.
The [readable pinned original](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/IntegerUnitsHerbrand.lean>)
is registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
and `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

Every original name below has prefix `LocalClassFieldTheory.`; every adapted
name has prefix `Langlands.NYLL.LocalClassFieldTheory.`.

| Unit | Original name | Adapted name | Source statement | Source proof |
| --- | --- | --- | --- | --- |
| M149.001 | `chosenNormalBasisIntegerUnitsHerbrand_shortExact` | `chosenNormalBasisIntegerUnitsHerbrand_shortExactStatement` | 48–67 | 68–92 |
| M149.002 | `integerUnits_herbrandQuotient_eq_one_of_chosenNormalBasis` | `integerUnits_herbrandQuotient_eq_one_of_chosenNormalBasisStatement` | 98–116 | 117–157 |
| M149.003 | `exists_integerUnits_herbrandQuotient_eq_one_of_large_chosenNormalBasisLevel` | `exists_integerUnits_herbrandQuotient_eq_one_of_large_chosenNormalBasisLevelStatement` | 165–181 | 182–187 |

The three propositions retain the common source section telescope at lines
39–44 explicitly and in order:

```lean
(K L : Type)
[Field K] [Field L] [Algebra K L]
[FiniteDimensional K L] [IsGalois K L]
[ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
[ValuativeRel L]
[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
[IsIntegralClosure 𝒪[L] 𝒪[K] L]
```

Both types are in universe zero, as in the original `Type` binders.
M149.001 then binds explicit `(n : Nat)`, `(V : Subgroup 𝒪[L]ˣ)` and the
carrier equality `(hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)`.
It installs, in source order, the actual action on `V`, the integer-unit
action and the quotient action. Its five conjuncts assert equivariance of
the inclusion, equivariance of the quotient map, the elementwise
kernel/range equivalence, injectivity of the inclusion and surjectivity of
the quotient map. The inclusion and projection are the published `V.subtype`
and `QuotientGroup.mk' V` constructions.

M149.002 has the same explicit `n`, `V` and `hV`, followed by the original
explicit hypotheses in this order:

```lean
(hfinite : Finite (𝒪[L]ˣ ⧸ V))
(g : Gal(L/K))
(hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g)
(hH0 :
  letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
  Subsingleton (HerbrandH0 (Gal(L / K)) V))
(hHminusOne :
  letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
  Subsingleton (HerbrandHMinusOne (Gal(L / K)) V g))
```

Its conclusion keeps all three source `letI` expressions, then asserts
existence of `hU : HerbrandQuotientDefined (Gal(L / K)) 𝒪[L]ˣ g` with the
actual integer-unit Herbrand quotient equal to `1`. The witnesses `hU.1`
and `hU.2` are used explicitly as finiteness instances in the quotient
expression. `HerbrandQuotientDefined` is the conjunction of finiteness of
the actual degree-zero and degree-minus-one quotients; `herbrandQuotient`
is the rational ratio of their natural-number cardinalities. The
subsingleton inputs concern the subgroup `V`, and the conclusion concerns
all integer units.

M149.003 appends exactly the source instance binders at lines 159–160:
`[TopologicalSpace L] [IsNonarchimedeanLocalField L]`
and `[Module.Finite 𝒪[K] 𝒪[L]]`. Its body preserves
`∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ V hV g`, followed by the generator,
degree-zero and degree-minus-one subsingleton premises and the same
integer-unit conclusion as M149.002. In particular, this target remains
conditional on the two subgroup cohomology premises at each level.

The imports reuse the independently published M145.006 subgroup action
and M145.010 quotient action. Their actual stability proof M145.005
remains in the constructions; neither is replaced by an assumed action.
The Herbrand finiteness predicate and quotient definition are reused from
their published focused modules. The source proofs use further exactness,
finiteness and multiplicativity theorems; those proofs are separate work
and are omitted here.

Modifications: prefix the namespace with `Langlands.NYLL`, extract the three
related statements into this pair, replace each theorem by a `Prop`-valued
definition with a `Statement` suffix, make the full effective section
telescope explicit and narrow the imports to the published constructions.
Preserve all own binders, binder kinds, conclusion expressions and
local-instance order. The source docstrings at lines 46–47, 94–97 and
162–164 are retained; they describe the intended theorems, while this
contribution supplies their targets only. A file-local
`linter.unusedVariables false` suppresses warnings for intentionally
retained source proof hypotheses, without changing the propositions.
Omit the source proofs and unrelated commands. No global instance is
introduced. The original Apache-2.0 copyright and author header and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.

These are supporting statement targets. They supply no proof of exactness,
Herbrand multiplicativity, class formation or reciprocity and do not
complete the larger task. Development checks use environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`.
