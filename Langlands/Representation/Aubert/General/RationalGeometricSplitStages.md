# Actual rational geometric subgroups for split stages

This internal adapter constructs the intermediate subgroup for the published
split-stages retraction, using the original rational standard subgroups and
their actual Levi projection. It is a prerequisite for the proper-intersection
geometric comparison, and supplies no integral or normalized graded comparison.

Write `Q = P_I`, `L = M_I`, `r = d.projection` and
`s = Subgroup.inclusion d.levi_le`. Let
`H = (P_I ∩ n P_J n⁻¹).subgroupOf P_I` and
`K = (M_I ∩ n P_J n⁻¹).subgroupOf M_I`, with the literal
`geometricTargetIntersection` definitions. The definition
`geometricSplitIntermediate` is `P = K.comap r`.

The kernel lies in `P` because its projection is the identity. Restricting `P`
along the actual Levi section gives exactly `K`, since `r(s(m)) = m`.
The same section has values in `H` on all of `P.comap s`.
The original projection-preservation theorem puts `H` inside `P`.
These are the subgroup and section hypotheses of `splitStagesCompactEquiv`.

`geometricSplitQuotientEquiv` identifies `P.comap s` with the literal `K`
without changing the original Levi point. `geometricSplitRetraction` composes
the published `splitStagesRetraction` with this quotient identification.
It sends each intermediate point to its original projection, and restricts
to exactly `stabilizerProjection` on `H`.

The section and the quotient identification in both directions are continuous
for the induced subgroup topologies. The retraction, stabilizer projection and
source-radical projection are continuous whenever the respective original
Levi projection is continuous. For any ambient topological group structure,
closedness of the displayed original parabolics and target Levi gives
closedness of `H` and `K`; continuity of the original projection then gives
closedness of `P`. The canonical evaluation topology in the rational
expansion target is a specialization of these statements.

The field and normalizer-point scopes are those of the imported projection
module. The inclusion `H ≤ P` and its restriction formula use the
standard-cocharacter, connected reductive, maximal split torus, generic
cocharacter and point-normalizer comparison inputs. All other constructions
use only the displayed decomposition, subgroup operations and induced
topologies. No minimality, intersection-decomposition or finite-length
premise is used.

The direct dependencies are `IsSemidirectDecomposition.projection_levi`,
`stabilizerProjection`, `stabilizerProjection_apply`,
`sourceRadicalProjection`, `Induction.splitStagesRetraction`,
`isClosed_geometricTargetIntersection` and Mathlib subgroup and continuity
constructions. Five private generic lemmas implement kernel containment in
an inverse image, restriction along a section, membership in the stabilizer,
containment from a restricted homomorphism, and equality of restrictions from
their ambient values. They keep elementary equality elimination separate from
the large rational-point definitions.

Transitively, the projection-preservation argument uses
`projection_mem_conjugate_parabolic`, closed stable dynamic limits,
common-torus conjugation, standard cocharacters and the comparison of the
original Levi projection with the dynamic limit, as documented in
`RationalGeometricStabilizerProjection.md`. The split-stages retraction uses
the split law and kernel containment to restrict the same homomorphism;
its definition invokes no integral comparison. The closedness theorem uses
the homeomorphism given by inner conjugation. The implemented proof chain
uses no geometric expansion, adjointness, cuspidal support, character
independence or Langlands classification, including Aubert Proposition 3.2
or its defective original application to Theorem 3.6. The imported-module
closure is broader than these proof-body dependencies; importing the
representation functor definitions does not discharge their targets.

Local compactness, compact-open subgroup bases, Borel structures, regular
left/right Haar measures and compatible quotient measure remain to be supplied
at the integral application. The inner coefficient quotient must still be
identified with the actual source-intersection Jacquet object. Both Haar
corrections, distinct-radical modulus comparison, smooth realization and
compact-induction/full-induction comparison remain. The exact rational
geometric K0 expansion is open.
