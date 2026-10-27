# Native maximal-ideal adic completeness

This module proves the published closed proposition
`Langlands.NYLL.ValuationTheory.Valuations.RankOneDiscreteValuationSubringIsAdicCompleteStatement.{u,v}`
as
`Langlands.NYLL.ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdicComplete.{u,v}`.
Its complete unapplied theorem type is exactly the named statement. Every
mathematical parameter is quantified inside that statement, and the field and
value group keep independent universe levels `u` and `v`.

## Target and supplied structures

For every `{K : Type u} [Field K] {Gamma : Type v}
[LinearOrderedCommGroupWithZero Gamma] [Valued K Gamma]`,
`[(Valued.v : Valuation K Gamma).IsRankOneDiscrete]` and `[CompleteSpace K]`,
put `val = (Valued.v : Valuation K Gamma)`, `A = val.valuationSubring` and
`m = IsLocalRing.maximalIdeal A`. The theorem proves `IsAdicComplete m A`.
This is Mathlib's algebraic notion: `A` is `m`-adically Hausdorff and
`m`-adically precomplete.

`CompleteSpace K` refers to the uniformity that the supplied `Valued` instance
puts on `K`. The subring `A` carries the native subtype topology and the
induced subtype uniformity. The proof installs no other topology or
uniformity. It assumes neither adicity nor completeness of `A`, Henselianity,
a finite residue field, local compactness, a nonarchimedean local field
structure, a complete discretely valued field bundle, or surjectivity of the
valuation onto `Gamma`.

## Implemented proof

1. The imported M247.002 theorem
   `rankOneDiscreteValuationSubring_isAdic.{u, v}` gives `IsAdic m` for the
   native subtype topology on `A`.
2. Instance search finds no `IsUniformAddGroup` on `A`, so the proof installs
   one locally. It is Mathlib's `AddSubgroup.isUniformAddGroup` for the
   additive subgroup underlying `A`, which comes from the induced subtype
   uniformity.
3. `Valued.isClosed_valuationSubring K` shows that `A` is closed in `K`.
   Mathlib's `IsClosed.completeSpace_coe` takes this closedness as an
   instance-implicit argument and is given it explicitly. It turns
   `CompleteSpace K` into `CompleteSpace A` for the induced uniformity.
4. Mathlib's `IsAdic.isAdicComplete_iff` says that, for an adic ideal in a
   commutative ring with a uniform additive group structure,
   `IsAdicComplete m A` is equivalent to `CompleteSpace A ∧ T2Space A`.
   The right-to-left direction finishes the proof. Instance search supplies
   `CompleteSpace A` from step 3. It supplies `T2Space A` through Mathlib's
   subtype instance `instT2SpaceSubtype` from the `T2Space` structure of the
   valued field `K`.

The original also installs a local `IsTopologicalRing A`. The approved
signature of `IsAdic.isAdicComplete_iff` needs only `CommRing`, `UniformSpace`
and `IsUniformAddGroup`, so that instance is omitted here. The imported
adicity proof keeps its own local topological-ring instance, which also comes
from the native subtype topology.

## Checks

`lean_check` in the approved environment compiled the module with no errors or
warnings. It found exactly the axioms `propext`, `Classical.choice` and
`Quot.sound`, and level parameters `[u, v]`. A separate private check module,
not part of this submission, confirmed that the declared type is
syntactically `Expr.const` of
`RankOneDiscreteValuationSubringIsAdicCompleteStatement` at
`[Level.param u, Level.param v]`.

## Source correspondence and imports

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Valuation/ValuedAdicComplete.lean`, lines 117–138](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/ValuedAdicComplete.lean#L117-L138),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, unit M247.003.
The proof follows the original route through closedness, inherited
completeness, the inherited Hausdorff property, and the adic-completeness
criterion.

| Original name | Name here |
| --- | --- |
| `ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdicComplete` | `Langlands.NYLL.ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdicComplete` (proof of `RankOneDiscreteValuationSubringIsAdicCompleteStatement`) |
| `ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdic` | `Langlands.NYLL.ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdic` (imported published M247.002 proof) |

The only direct import is
`Langlands.NYLL.ValuedFieldTheory.Valuation.ValuedAdicComplete.AdicProof`.
It supplies the published adicity theorem and, through its own imports, the
unchanged target statement and the Mathlib modules used above
(`Mathlib.RingTheory.AdicCompletion.Topology`,
`Mathlib.Topology.Algebra.Valued.ValuationTopology` and
`Mathlib.Topology.Algebra.Valued.ValuedField`). No external repository module
is imported. The adicity proof is imported rather than copied.

This module excludes M247.001 (the discrete valuation ring result) and
M247.004 (the `CompleteDVF` construction). It also excludes Henselian or
extension results and every reciprocity claim.

## Attribution and modifications

The original source is registered as
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original file was read and its SHA256 checked as
`183b8dd3fb4910ec7378d280839436826d06929fa4e8081dd460e89cbd05d5fb`.
No source-specific errata file exists under the project notes or the current
Library notes.

The original copyright and author header is kept verbatim. The existing,
unmodified [LICENSE](../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../licenses/NYLL/NOTICE) still apply. Their SHA256 values
are `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

Worker 738 extracted this proof on 27 October 2026 and made these changes:

- added the `Langlands.NYLL` namespace prefix;
- stated the theorem as the published closed target;
- imported the published M247.002 proof instead of the original module;
- passed the closedness argument of `IsClosed.completeSpace_coe` explicitly;
- removed the unused local topological-ring instance;
- wrote this explanation.

No unpublished draft by another worker was reused. Worker 106 supplied the
task and the source routing. The approved environment is Lean 4.34.0 and
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
