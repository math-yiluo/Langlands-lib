# Geometric full and away Tate modules are free of rank 2g

`Langlands.AbelianScheme.Tate.geometricAdelicRank` proves exactly the
published `Langlands.AbelianScheme.Tate.GeometricAdelicRankStatement.{u}`
from [GeometricAdelicRankStatement](GeometricAdelicRankStatement.md).
The arbitrary universe, actual abelian schemes and geometric points, specified
relative dimension and all original unit hypotheses are retained. The integral
and rational conclusions use the actual full and away torsion-section inverse
limits and their existing scalar actions.

Worker 195 authored the proof and its explanation in Task 195's shared draft
revision 2, `Task195/AdelicRankDraft.lean` and its companion. Worker 1918 prepared
this pair for Task 2971, placed its algebraic helpers in
`Langlands.TateAdelicRank`, and exposed the final theorem in the established
`Langlands.AbelianScheme.Tate` namespace. The published statement and its import
closure are unchanged.

The full scalar coordinates are the published canonical maps `toPadic`.
Their bijectivity follows from the published normalized continuous product
comparison: density of the integer residue families identifies that comparison
with these canonical coordinates. The away coordinates are injective because
prime-power reductions determine each allowed residue. This argument follows
the internal proof in `PrimeToIntegralProfiniteIntegerComparisonProof`;
its private lemma is not imported by name. For surjectivity, extend an away
prime family by zero at the excluded primes, use full surjectivity, and
restrict the resulting residue family. This applies to all natural moduli,
including an empty retained-prime set.

The two scalar compatibility lemmas inspect actual prime-power torsion
coordinates and use the exact `toZModPow_toPadic` formulas. They concern the
published full and away residue actions and the actual Tate coordinate maps.
The generic assembly construction combines a product scalar equivalence,
a scalar-compatible additive coordinate equivalence, and chosen local finite
free equivalences. It interchanges the finite basis index with the prime
index and proves linearity explicitly.

All material here is an internal derivation from published Library interfaces
and Mathlib algebra. Source conventions and the geometric rank input are
documented in the unchanged statement Markdown and in the imported prime-adic
rank proof. The assembly asserts no continuity or monodromy compatibility of
chosen bases.

The integral full and away equivalences instantiate the generic assembly using
the published actual additive comparisons and the coordinate scalar lemmas.
At a geometric point, each local basis is chosen from the published
`geometricPrimeAdicRank`, using the corresponding base-unit hypothesis.
No basis is assumed by these geometric constructions.

The rationalization argument uses `TensorProduct.piRight` only for the finite
basis index. On pure tensors, its compatibility with
`TateScalarExtension.action` is the tensor-product multiplication formula;
additivity extends the identity to all tensors. Rationalizing the inverse
integral linear equivalence preserves that action by the published
`TateScalarExtension.map_action`. Coordinatewise scalar comparison then
transports the action along the explicitly supplied rational ring equivalence.

The final theorem applies the two geometric integral equivalences and then
`rationalFree` to each explicitly quantified scalar-comparison witness. The
transported module action agrees definitionally with the action required by
that generic construction: it is precisely the published `finiteAdeleModule`
or `primeToFiniteAdeleModule`. No new adelic action is defined. The proof
retains every original hypothesis, handles every natural modulus and `g = 0`,
and leaves the statement and all its dependencies unchanged.

The cases `m = 1` and `m = 0` require no separate assumption: for `m = 1`
all primes are retained, whereas for `m = 0` the retained-prime set is empty.
The assembly works for the empty product of scalar rings and the corresponding
zero modules. The finite index `Fin (2 * g)` is also allowed to be empty. These
are existence equivalences; they assert no uniqueness of numerical rank over
the zero ring.

The full and away prime-coordinate scalar compatibility lemmas reuse
`Langlands.GroupScheme.Tate.PrimeComparison.fullToPrime_smul` and
`awayToPrime_smul` from `PrimeScalars`, with identical parameters and conclusions.
