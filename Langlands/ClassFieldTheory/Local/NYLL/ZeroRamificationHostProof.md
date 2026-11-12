# Zero-depth ramification in terms of supplied local-field data: proof

This module proves
`Langlands.LocalClassField.NYLL.zeroUpperRamificationHost :
Langlands.LocalClassField.NYLL.ZeroUpperRamificationHostStatement`.
The target is published in `ZeroRamificationHostStatement.lean`. For a finite
Galois extension of universe-zero p-adic fields, it says that `σ` lies in the
NYLL zeroth upper ramification group built from `TF` exactly when
`TE.discreteValuation (σ x - x) < 1` for every `x` with
`TE.discreteValuation x ≤ 1`. Here `TE` is an arbitrary supplied realization of
the extension. The theorem has exactly the published type and adds no premise.

## Two private helper lemmas

Both helpers hold for any supplied `T : F.TopologicalData` in any universe. They
install `T.topology`, `T.valuativeRel` and `T.localField` and write `e` for
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier`. By definition,
`T.discreteValuation` is `ValuativeRel.valuation F.Carrier` followed by `e`.

- `mem_integers_iff`: `x ∈ T.Integers ↔ T.discreteValuation x ≤ 1`. Membership
  in `T.Integers` is `ValuativeRel.valuation F.Carrier x ≤ 1`. Since `e` maps
  `1` to `1` and is strictly monotone, it preserves and reflects `≤ 1`.
- `mem_maximalIdeal_iff`: for `a : T.Integers`, membership in the maximal ideal
  holds iff `T.discreteValuation a < 1`. Maximal-ideal membership means `a` is
  not a unit. By Mathlib's `Valuation.Integer.not_isUnit_iff_valuation_lt_one`,
  this means `ValuativeRel.valuation F.Carrier a < 1`. Strict monotonicity of
  `e` turns this into the inequality for `T.discreteValuation`.

The first helper reproduces the short argument of the published
`Langlands.PadicField.TopologicalData.mem_integers_iff_discreteValuation_le_one`
in `Langlands.HarmonicAnalysis.Conductor`. The second uses the same
valuation/maximal-ideal translation as the published
`Langlands.LocalClassField.NYLL.suppliedResidueCongruence` in
`Langlands.ClassFieldTheory.Local.NYLL.SuppliedResidueProof`. These two
theorems are provenance references for the local arguments, rather than
applications in this proof.

## Main proof

1. Introduce all binders. Install on `F.Carrier` the topology, valuative
   relation and local-field structure of `TF`, as in the statement, and on
   `E.Carrier` those of `TE`.
2. **Valuation extension.** Take the instance
   `Valuation.HasExtension (ValuativeRel.valuation F.Carrier) (ValuativeRel.valuation E.Carrier)`
   from the published `suppliedRelativeValuationExtension p F E TF TE`.
3. **Integral closure and finiteness.** The published
   `relativeIntegerStructure p F E TF TE` gives `IsIntegralClosure` and
   `Module.Finite` for the explicit algebra structures
   `relativeIntegerFieldAlgebra TF : Algebra TF.Integers E.Carrier` and
   `relativeIntegerAlgebra TF TE : Algebra TF.Integers TE.Integers`.
   M328.002 needs these properties for Mathlib's instances, namely
   `Algebra.ofSubsemiring 𝒪[F]` on `E` and
   `Valuation.HasExtension.instAlgebraInteger` on `𝒪[E]`. In each case the two
   algebra maps are the same function `x ↦ algebraMap F E x`. So
   `Algebra.algebra_ext` (with `rfl` on each element) proves the two equalities
   `hB` and `hA` of algebra structures. The structures are equal but not
   definitionally equal, since their scalar actions are defined differently.
   The hypotheses are first ascribed with their explicit instances and then
   rewritten with `hB`, respectively `hA`. Because `IsIntegralClosure A R B` has
   no `Algebra R A` argument, only `hB` is needed for it. Only `hA` is needed for
   `Module.Finite`, whose module structure comes from the algebra.
4. **Residue kernel.** Rewrite with the published
   `localUpperRamificationGroup_zero_eq_residue_ker F.Carrier E.Carrier`
   (M328.002) and then with
   `galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal`
   (M160.018). The left side becomes: for every `x : 𝒪[E]`, the difference
   `galoisGroupIntegerRingEquivOfIsIntegralClosure F E σ x - x` lies in the
   maximal ideal.
5. **Evaluation.** By `AddSubgroupClass.coe_sub` and the published
   `galoisGroupIntegerRingEquivOfIsIntegralClosure_apply` (M139.003), that
   difference has value `σ x - x` in `E.Carrier`.
6. **Translation.** For the forward direction, take `x` with
   `TE.discreteValuation x ≤ 1`. Then `x ∈ TE.Integers` by `mem_integers_iff`,
   and `mem_maximalIdeal_iff` with step 5 gives
   `TE.discreteValuation (σ x - x) < 1`. For the converse, apply the hypothesis
   to the value of an integral `x`, whose discrete valuation is at most one by
   `mem_integers_iff`, and convert back with `mem_maximalIdeal_iff`.

The comparison between NYLL's chosen extension valuation and the supplied one
takes place entirely inside the published M328.002. That theorem identifies
the group with the residue kernel of the instance valuation, here the one from
`TE`.

## Published inputs and modules

The target is the unchanged
`Langlands.LocalClassField.NYLL.ZeroUpperRamificationHostStatement` in
`Langlands.ClassFieldTheory.Local.NYLL.ZeroRamificationHostStatement`.
The five published Library theorems directly applied by the main proof are:

| Fully qualified theorem | Module |
| --- | --- |
| `Langlands.LocalClassField.NYLL.suppliedRelativeValuationExtension` | `Langlands.ClassFieldTheory.Local.NYLL.SuppliedValuationProof` |
| `Langlands.LocalClassField.NYLL.relativeIntegerStructure` | `Langlands.ClassFieldTheory.Local.NYLL.RelativeIntegerStructureProof` |
| `Langlands.NYLL.RamificationTheory.LocalField.localUpperRamificationGroup_zero_eq_residue_ker` | `Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.ResidueInertia.Proofs` |
| `Langlands.NYLL.LocalFieldTheory.galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal` | `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois.KernelProofs` |
| `Langlands.NYLL.LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure_apply` | `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.Proofs` |

The remaining named theorem applications are from the pinned Mathlib:

| Theorem | Module |
| --- | --- |
| `Algebra.algebra_ext` | `Mathlib.Algebra.Algebra.Defs` |
| `AddSubgroupClass.coe_sub` | `Mathlib.Algebra.Group.Subgroup.Defs` |
| `IsLocalRing.mem_maximalIdeal` | `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic` |
| `Valuation.Integer.not_isUnit_iff_valuation_lt_one` | `Mathlib.RingTheory.Valuation.Integers` |
| `map_one` | `Mathlib.Algebra.Group.Hom.Defs` |
| `StrictMono.le_iff_le`, `StrictMono.lt_iff_lt` | `Mathlib.Order.Monotone.Basic` |

The order isomorphism
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt` is defined in
`Mathlib.NumberTheory.LocalField.Basic`. The supplied discrete valuation
is defined in `Langlands.LocalField.Normalization.Definitions`.
All imports and the statement's Lean/Markdown pair are unchanged. Every
instance installed by this proof is local to its theorem; no global
instance is declared.

## Provenance and authorship

This is an internal derived host formulation of the published residue-kernel
theorems, not a new transcription of an original-literature statement.
Worker 928 (formerly Worker 10) wrote the Lean proof and its initial explanation
for Task 928. Worker 122 reused that complete Lean file without changes from
the immutable shared draft revision 2 of task
`34dfcbc7-f6ed-46fd-84e3-4d89df60fe8e`, checked the published inputs and
proof, and expanded the dependency citations and verification record for
Task 5267. The published NYLL modules retain their own original-source and
license documentation. No external source code is copied into this pair.

## Verification

`lean_check` in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` compiled this
module against the published statement at Library base
`230ec08a058832bd6941fa887c30897e4826429b` with zero errors or warnings.
The diagnostic is `b107e5bf-720d-45e4-abe3-c6ffd6e54ee4`.
Inspection of `zeroUpperRamificationHost` reported a theorem with no
universe parameters whose only axioms are `propext`, `Classical.choice` and
`Quot.sound`. The theorem is explicitly ascribed the exact closed published
proposition. These are development checks; independent proof review and
the candidate's exact-target validation and publication are separate.
