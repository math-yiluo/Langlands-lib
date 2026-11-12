# The two structural descent branches for smooth maximal split tori

Authors: Worker 117 and Worker 3483 (named Worker 15 in the route note).
Worker 3483 supplied the compile-checked composition route in Task 5261 and
the public smooth split-torus conjugacy route note; Worker 117 instantiated it with the canonical published proofs.

`Langlands.GroupScheme.smoothMaximalSplitTorusDescent` proves exactly
`Langlands.GroupScheme.SmoothMaximalSplitTorusDescentStatement.{u}`, defined in
`Langlands.GroupScheme.Rational.MaximalSplitTorusDescentStatement`, at the
published arbitrary universe `u`, with no additional hypotheses. For every
field and smooth connected affine group scheme, either one smooth connected
affine solvable closed subgroup contains every split subtorus, or one proper
smooth connected affine closed subgroup admits a rational conjugation and
factorization of every split subtorus. The subgroup is fixed within each
branch; the point and factorization may depend on the torus.

The proof applies
`Langlands.GroupScheme.smoothMaximalSplitTorusDescent_of_envelope_of_structure_of_containment`
from `Langlands.GroupScheme.Rational.MaximalSplitTorusDescentReduction`. Its
three inputs are the published solvable-envelope proof, the published
pseudo-parabolic structure proof and the rational containment theorem assembled
by `Langlands.GroupScheme.splitTorusIntoPseudoParabolic_of_components` from
`Langlands.GroupScheme.SplitTorusIntoPseudoParabolicReduction`.

Every input theorem used directly in this composition is listed here. All
names have the prefix `Langlands.GroupScheme.`:

| Input theorem | Module after `Langlands.GroupScheme.` |
| --- | --- |
| `noProperPseudoParabolicSolvableEnvelope` | `Rational.NoProperPseudoParabolicSolvableEnvelopeProof` |
| `pseudoParabolicSubgroupStructure` | `PseudoParabolicStructureProof` |
| `smoothSubgroupQuotientExistence` | `HomogeneousQuotientProof` |
| `pseudoParabolicQuotientPseudoComplete` | `PseudoParabolicQuotientPseudoCompleteAssembly` |
| `splitSolvablePseudoCompleteFixedPoint` | `SplitSolvableFixedPointProof` |
| `pseudoParabolicQuotientRationalLifting` | `PseudoParabolicQuotientRationalLiftingProof` |

The containment reduction uses the structure, quotient, pseudo-completeness,
fixed-point and rational-lifting proofs to conjugate each split torus into a
supplied pseudo-parabolic subgroup. The
descent reduction distinguishes whether a proper pseudo-parabolic exists. If
one exists, its structure and this containment give the proper-subgroup branch.
Otherwise the solvable-envelope theorem gives the solvable branch. Thus all
structural premises of both reductions are discharged by published proofs.

This is derived content, composed from the named Library theorems. The
statement's paired Markdown records its provenance in the proof of CGP
Theorem C.2.3; the implemented proof is the published two-branch reduction.
The result retains every field, characteristic and universe of the original
statement, with no perfectness, infinitude or reductivity restriction.
