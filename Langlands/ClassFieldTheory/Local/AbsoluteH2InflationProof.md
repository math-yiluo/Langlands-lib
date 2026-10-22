# Finite-to-absolute degree-two inflation and restriction exactness

Author: Worker 63.

`Langlands.ClassFieldTheory.Local.absoluteH2InflationExactness` proves exactly
`AbsoluteH2InflationExactness.{u}`. For every characteristic-zero field `K` and
finite Galois intermediate field `E` of `AlgebraicClosure K`, in an arbitrary
common universe, `closureInflation K E 2` is injective and its additive range
equals the additive kernel of `absoluteRestriction K E 2`. The latter map uses
the supplied `Algebra (AlgebraicClosure K) (AlgebraicClosure E)` and scalar
tower over `K`. No agreement with the canonical embedding of `E` into its own
closure is assumed. The theorem asserts no surjectivity of restriction.

All finite exactness, finite-to-continuous comparison, limit, and closure
transport inputs are separately published proofs imported by module name.
The target and its dependencies are unchanged. No vanishing, exactness, or
comparison premise is added to the target.

## Finite stages

The internal lemma `AbsoluteH2Assembly.linearExactness_of_comparison`
transfers injectivity and a linear range/kernel equality across three linear
equivalences and two commuting squares. Injectivity is detected by the source
equivalence. To transfer exactness, the target equivalence detects zero, and
the inverse source equivalence transports a preimage supplied by the known
range/kernel equality. This is internal diagram bookkeeping.

`AbsoluteH2Assembly.finiteStageExactness` fixes
`H = finiteGaloisFixingSubgroup K E` and an open normal subgroup `N ≤ H`.
It uses the actual finite Galois field `finiteStageFixedField K N`, with
`finiteStageRestrictedAlgebra` and `finiteStageRestrictedTowerBase` giving
the canonical inclusion of `E` and its base scalar tower. The three linear
equivalences come from `finiteGaloisStageRelativeIso`,
`finiteStageRelativeIso`, and `finiteStageRestrictedRelativeIso`.
The two commuting squares are the published
`finiteGaloisStageRelativeIso_inflation` and
`finiteStageRelativeIso_restriction`, evaluated at each class. The inclusion
algebras used in these two modules agree definitionally. The published
`finiteRelativeH2InflationExactness K E (finiteStageFixedField K N)` supplies
finite exactness. Its proof has already discharged the Hilbert 90 input;
this module assumes no first-cohomology vanishing.

## Passage to continuous cohomology

`AbsoluteH2Assembly.closureInflationExactness` is an unconditional intermediate
result with only the field, characteristic-zero, and finite Galois hypotheses.
It identifies the range of `closureInflation K E 2` with the kernel of the
actual `Langlands.Continuous.continuousRestriction` to the fixing subgroup,
and also proves inflation injective. It needs neither a second algebraic
closure nor a compatible embedding into one.

The proof applies published `finiteStageExactnessLimit` to the genuine discrete
unit module `absoluteUnitDiscreteModule K`, the compact absolute Galois group,
and `H`. The preceding finite-stage theorem supplies its hypothesis for every
`N ≤ H`. The additive equivalence extracted from `finiteGaloisStageRelativeIso`
identifies the source with `relativeCohomology K E 2`; the published identity
`finiteGaloisStageRelativeIso_closureInflation` identifies the canonical stage
map with `closureInflation`. Applying the inverse source equivalence transfers
injectivity. Membership in the linear range/kernel equality supplied by the
limit theorem gives each direction of the asserted additive range/kernel
equality. This is the finite-to-continuous passage for the actual maps, rather
than an assumed exactness property of an alternative cohomology model.

## Absolute restriction

The final theorem preserves the intermediate injectivity result and identifies
its kernel with that of `absoluteRestriction`. After taking membership and
expressing it as a zero equation, the reversed published equivalence
`absoluteRestriction_eq_zero_iff_subgroup K E 2 x` gives the required equality.
The fixing subgroup of `finiteGaloisFixingSubgroup K E` and its restriction map
are definitionally the subgroup and underlying cohomology map in that theorem.
Thus no additional wrapper or new closure comparison is required.

The imported closure transport constructs an equivalence using the specified
`K`-compatible closure embedding. Its normality argument handles the possible
twist of the copy of `E`, so this application introduces no stronger
compatibility hypothesis and does not assert equality of two embeddings.

## Provenance and attribution

The target is the characteristic-zero finite-extension specialization of
Jean-Pierre Serre, *Local Fields* (1979), Chapter X, section 4, Corollary to
Proposition 6, printed page 156 / PDF page 162. Section 3, printed page 154 /
PDF page 160, describes passage from finite stages to continuous cohomology.
The registered original is `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 63 read PDF pages 160–162 during this task. The implemented proof follows
the finite-to-limit route using the published interfaces described above.
The precise Lean diagram and additive-kernel conversions are internal lemmas,
not separately attributed source statements.

The new assembly is by Worker 63. Published inputs retain their authorship:
Worker 21 (`FiniteStageExactnessLimitProof`), Worker 58
(`RelativeH2InflationProof`), Worker 68 (`FixedFieldStages`), Worker 104 with
Workers 29 and 54 (`FixedFieldStageInflation`), Worker 54
(`FixedFieldStageClosureInflation`), Worker 29 (`FixedFieldStageRestriction`),
and Worker 134 (`ClosureCohomologyTransport`). Their own pairs credit further
dependencies. They are reused by imports; no unpublished proof draft is copied.
