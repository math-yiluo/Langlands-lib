# NYLL convergence statements for Galois norms and coboundaries

Worker 197 adapts M150.005 and M150.006 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisInfiniteProduct.lean`.
The readable pinned original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`,
registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The supplemental registration is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
There is no applicable NYLL entry in the Library's `notes/errata/`.

| Unit | Original declaration in `LocalClassFieldTheory` | Source lines | Adapted declaration in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- | --- | --- |
| M150.005 | `tendsto_galoisGroupIntegerUnits_tateNorm_of_tendsto` | 137–169; target 137–148 | `tendsto_galoisGroupIntegerUnits_tateNorm_of_tendstoStatement` |
| M150.006 | `tendsto_galoisGroupIntegerUnits_sigmaMinusOne_of_tendsto` | 177–226; target 177–188 | `tendsto_galoisGroupIntegerUnits_sigmaMinusOne_of_tendstoStatement` |

Both propositions retain the exact source target: if a sequence of integer
units converges after coercion to the integer ring, its finite Tate norms,
respectively its multiplicative coboundaries for a specified Galois
automorphism, converge after the same coercion to the operation on the limit.
Each target retains the original `letI` installing the actual integer-unit
Galois action. Convergence is measured in the integer ring with its topology
induced by the supplied local-field structure on `L`.

The shared universe is `u`. For M150.005 the full source telescope, in order,
is explicit `(K L : Type u)`, instances `[Field K] [Field L] [Algebra K L]
[FiniteDimensional K L] [ValuativeRel K] [ValuativeRel L]
[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`,
then the theorem's own instances `[UniformSpace L] [IsUniformAddGroup L]
[IsNonarchimedeanLocalField L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]`, followed by
explicit `f`, `x` and `hf` exactly as in the Lean file. The source section
variables are at lines 30–34. The `omit` command at line 133 removes
`IsGalois K L`, `TopologicalSpace K` and `IsNonarchimedeanLocalField K`.
Finite dimensionality remains, providing finiteness of the automorphism group
for the finite Tate norm.

M150.006 has the same instance order with `FiniteDimensional K L` also
omitted, followed by explicit `(g : Gal(L/K))`, `f`, `x` and `hf`.
The source `omit` command at lines 171–172 removes finite dimensionality,
the Galois hypothesis and both topology/local-field hypotheses on `K`.
The explicit convergence premises `hf` are retained even though each target
conclusion does not depend on its premise's proof term.

The focused imports reuse
`Langlands.NYLL.LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure`
from `ClassFormation.Valuation.IntegerDefinitions`, the namespaced adaptation
of source `Valuation.lean`, lines 52–60, and
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.tateNorm` and
`sigmaMinusOne` from
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Definitions`.
Mathlib's local-field import supplies the original topology and local-field
classes. The actual action is installed locally; no global instance is added.

Modifications are the `Langlands.NYLL` namespace prefix, `Statement` suffixes,
replacement of both theorem proofs by `Prop`-valued definitions of their
targets, and extraction into this focused pair. Full effective theorem
telescopes are explicit to prevent `def` from dropping ambient instances.
Unused original imports, namespace openings and unrelated commands are omitted.
The unused-variable linter is disabled separately for each definition to retain
the named source premise `hf`; this does not change either proposition.
No proof of either target or extra assumption is introduced.

The copyright and author header is retained. The Apache-2.0
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain applicable. These
supporting statements prove no class-formation or reciprocity theorem.
