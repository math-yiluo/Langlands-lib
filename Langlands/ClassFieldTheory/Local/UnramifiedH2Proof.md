# Exhaustion of actual absolute H2 by finite unramified extensions

Author: Worker 26.

`Langlands.ClassFieldTheory.Local.unramifiedH2Exhaustion` proves exactly
`Langlands.ClassFieldTheory.Local.UnramifiedH2Exhaustion.{u}`. For every prime
`p`, every `F : PadicField.{u} p` and every element `x` of the actual continuous
group `absoluteCohomology F.Carrier 2`, it produces a finite Galois intermediate
field `E` in the given algebraic closure. The canonical absolute ramification
indices of `F` and `E.asPadicField (p := p)` agree, and `x` belongs to the range
of the existing `closureInflation F.Carrier E.field 2`. The common universe is
arbitrary, and the theorem has no additional hypotheses.

The proof uses these published inputs through their Lean declarations:

- `inertiaH2Vanishing`, in [InertiaH2Proof](InertiaH2Proof.md), by Workers 37
  and 10, proves vanishing for the actual canonical inertia subgroup with
  its inherited topology and restricted discrete algebraic-closure units.
- `Langlands.Continuous.closedNormalRestrictionZeroDetection`, in
  [ClosedSubgroupDescentProof](../../Cohomology/Continuous/ClosedSubgroupDescentProof.md),
  whose Lean proof is by Worker 102 and explanation by Worker 284, descends a
  zero restriction to an open normal subgroup containing the original closed
  normal subgroup.
- `Langlands.PadicField.canonicalUnramifiedCriterion`, in
  [UnramifiedCriterionProof](../../Galois/Local/UnramifiedCriterionProof.md), by
  Worker 231, identifies the actual inertia fixing condition with equality of
  the canonical ramification indices.
- `AbsoluteH2Assembly.closureInflationExactness`, in
  [AbsoluteH2InflationProof](AbsoluteH2InflationProof.md), by Worker 63,
  identifies the range of the actual closure inflation with the additive
  kernel of continuous restriction to the intermediate field's fixing subgroup.

The private helper `exists_inertia_splitting_neighborhood` applies the descent
theorem to `absoluteUnitDiscreteModule F.Carrier` in degree two. Characteristic
zero comes from the existing p-adic algebra. Mathlib's absolute Galois group
provides compactness, Hausdorffness and total disconnectedness. The canonical
inertia subgroup is closed and normal by the published absolute Galois API.
The imported inertia vanishing theorem makes its restricted continuous
cohomology a subsingleton, so the restriction of `x` equals zero. Descent then
gives an open normal subgroup `N` containing inertia on which the same class
restricts to zero. The restricted coefficient object is definitionally the
one in `InertiaH2Vanishing`; the helper changes no action or topology.

The final theorem takes `M = finiteStageFixedField F.Carrier N`, using the
published [FixedFieldStages](FixedFieldStages.md) constructions by Worker 68.
Its existing instances supply finite dimensionality and the Galois property.
Mathlib's infinite Galois correspondence identifies `M.fixingSubgroup` with
`N.toSubgroup`. The proof packages this same field as
`FiniteIntermediateExtension`, with its existing `asPadicField` wrapper.
Since inertia lies in its fixing subgroup, the canonical unramified criterion
gives exactly the equality of ramification indices in the target.

Finally, `closureInflationExactness` rewrites membership in the additive range
of `closureInflation` as a zero restriction equation. The fixing-subgroup
identity transports the equation already supplied by descent to this same
subgroup. The local `zero_of_eq` argument performs that dependent transport.
The proof therefore obtains an actual relative degree-two preimage under the
specified inflation map. Its route uses the subgroup restriction kernel, so
it needs no second algebraic closure or choice of embedding into one.

This is a derived assembly of the published field, arithmetic, topology and
cohomology interfaces above. Its mathematical provenance is Jean-Pierre Serre,
*Local Fields*, Greenberg English translation, Springer GTM 67 (1979),
Chapter XII, Section 1, Theorem 1 (printed page 181 / PDF page 186), and
Section 3, Proposition 3 (printed page 184 / PDF page 189). The registered
original is `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Serre's vanishing over the maximal unramified field is supplied here by the
published actual inertia H2 theorem; the finite splitting step is implemented
through closed normal restriction descent and the fixed-field correspondence.
The conclusion is the elementwise inflation-range form of Proposition 3.
No identification with a separate central-simple-algebra Brauer group is used.
The source's supporting continuous and finite-stage conventions are in X.3–4,
printed pages 154–156 / PDF pages 160–162.

Worker 26 wrote this assembly. The inputs retain the authorship recorded in
their published pairs and are reused by import; no unpublished peer draft is
copied into this module. The target statement and all imported pairs remain
unchanged.
