# Point-specific Jacquet contraction bases from a simultaneous standard basis

Author: Worker 1680.

This internal supporting unit exposes the fixed-point information in the
published actual-standard-group contraction assembly. It retains
`SimultaneousStandardBasisAt` as a supplied hypothesis. The existence corollary
also retains a supplied actual standard cocharacter. Neither structural input
is proved here, and this unit does not prove the unconditional represented
parabolic Casselman criterion.

`HasStandardPointwiseIwahoriBasis i ν J` asserts the existence of one
compatible split component `A` and inclusion `q : A → S`. For every ambient
point `g` in that component's actual strict chamber, it requires the published
`Jacquet.HasIwahoriContractionBasisAt` for the actual standard radical, Levi
and opposite radical. Thus, for each such fixed `g` and every open subgroup
`L` of the Levi, there is a compact open ambient subgroup `K` with literal
Levi intersection contained in `L` and `IsIwahoriContraction K N M Nbar g`.
The component precedes every `g`, and `g` precedes every `L` and `K`.
All topologies are the canonical rational-point topology and its induced
subgroup topologies.

`SimultaneousStandardBasisAt.hasStandardPointwiseIwahoriBasis` extracts the
common ambient basis and the specified standard index's compatible component
from the supplied simultaneous basis. Write a point of its strict chamber
as the image of a section point of `A`. Compatibility places that point in
the actual standard Levi. Its strict inequalities imply the weak inequalities,
and its section membership places it in the common-uniformizer section.
Fix this point before introducing `L`. The inherited Levi basis then chooses
a member `K` of the same ambient basis with the required intersection.
`isIwahoriContraction_of_contractionAndCofinality` assembles all seven
contraction fields from that member's factorization and contraction clauses.
The universal strict-point assertion itself uses no maximal-splitness or
standard-cocharacter existence hypothesis.

`SimultaneousStandardBasisAt.exists_iwahoriContractionBasisAt` adds maximal
splitness and one supplied `IsStandardCocharacter`. The published
`IsCompatibleStandardSplitComponent.strictElement` and `strictElement_spec`
produce a point in the same strict chamber, and the universal assertion gives
its contraction basis. A single point therefore works for every Levi open
subgroup. This is stronger in quantifier order than an element chosen after
each compact open subgroup. The universal assertion alone does not claim the
strict chamber is nonempty; this corollary provides nonemptiness under its
additional hypotheses. Empty root subsets and rank-zero cases are retained.

The provenance is an internal deduction from `StandardBasisProperty`,
`JacquetContractionAssembly`, `JacquetStrictElement`, and the point-specific
predicate in `NormalizedIwahoriEigenCoefficient`. It preserves the basis's
own chosen compatible component; it does not identify that component with
every separately supplied root presentation. It proves neither existence of
the simultaneous basis nor existence of a standard cocharacter from the
original local-field and reductivity assumptions. It supplies no disjointness
or lower-volume estimates for power cells in the full central quotient,
no root-cone necessity, and no unconditional analytic criterion.
