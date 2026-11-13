# The rational-point operator with published structural inputs

Worker 3640 assembles the published rational-point operator without the
separate topology, root-system and subgroup-regularity premises of
`RationalAlternatingOperator`. This is a derived construction supporting
Family 1 of the general Aubert program. It does not prove finite-length
preservation or any duality identity.

The field `k : Type u` is an arbitrary nonarchimedean local field. The ambient
group scheme `G` is connected reductive, `i : T.toGrp ⟶ G` is a maximal split
torus, and `ν` is a generic cocharacter. There is no characteristic, splitness,
quasi-splitness or positive-relative-rank restriction. The topology on the
actual identity-test rational-point group `RationalPoint k G.X` is precisely
the published `RationalPointFamily.pointTopology`, definitionally the
canonical rational-point topology. No alternate topology is supplied.

The operator and its class formula obtain affineness and smoothness from
`IsConnectedReductive`; smoothness supplies local finite type. They use
`BruhatTits.localField_t2Space`, `rationalPoint_t2Space`,
`rationalPoint_locallyCompactSpace` and
`Plancherel.rationalPoints_nonarchimedeanGroup` for the required topological
properties. The monomorphism instance is the one from `IsMaximalSplitTorus`.

The published `GroupScheme.standardCocharacter` supplies the standard
cocharacters and their actual dynamic subgroup comparisons.
`canonicalStandardUnipotent_isClosed` applies
`standardUnipotent_isClosed_of_standardCocharacterStatement` to that theorem.
Closedness of the standard parabolic, continuity of the semidirect projection
and compact containment of the unipotent group are supplied respectively by
`standardParabolic_isClosed_of_standardCocharacterStatement`,
`continuous_standard_projection` and
`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`.
The last input also supplies unipotent unimodularity through the already
published normalization theorem.

Exactly two representation-theoretic inputs remain:
`DynamicInductionFiniteLengthStatement.{u, max (u + 1) v}` and
`DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v}`.
These are the existing general targets for normalized dynamic induction and
Jacquet restriction on actual rational points. They are explicit arguments;
they are neither asserted nor treated as structural facts.
`standardInduction_preservesFiniteLength_of_dynamic` and
`standardJacquet_preservesFiniteLength_of_dynamic` transport them to the
standard family by the actual subgroup equalities.
`canonicalStandardParabolicFiniteLength` applies the published exactness
construction to obtain the complete exact-K0 prerequisite for every index.
This helper retains the ambient affineness and local compactness,
nonarchimedean and Hausdorff typeclass arguments used by the generic operator;
the main constructor supplies them all from `hG` and the field instances.
The prerequisite includes preservation of all actual short exact sequences
of finite-length representations, including nonsplit ones.

`canonicalRationalAlternatingOperator` specializes
`rationalAlternatingOperator` with these data and with
`GroupScheme.relativeRootSystem`. Thus the finite index enumerates the literal
actual simple-relative-root subtype, rather than new root labels. The operator
acts on the existing exact `FiniteLengthGrothendieckGroup` of smooth complex
representations at carrier universe `max (u + 1) v`.
`canonicalRationalAlternatingOperator_ofRepresentation` gives the signed sum
of the actual `i_I r_I` representation classes with coefficient `(-1)^|I|`.
Its proof is the published rational-family class formula.
The empty simple-root set is permitted. In that case the displayed sum has
just its empty-index term with coefficient `+1`; no endpoint subgroup
identification or identity-operator assertion is added by this module.

The construction does not change any published proposition or proof-task
target. In particular the two finite-length preservation targets, the
contragredient finiteness results, the formal duality identities, corrected
complex theorems and general-to-GL comparisons retain their existing proof
obligations and owners. This derived assembly makes no new source translation
claim and uses only the named published constructions and the two displayed
unproved inputs.
