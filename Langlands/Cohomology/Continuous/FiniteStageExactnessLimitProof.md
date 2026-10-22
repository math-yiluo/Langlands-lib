# Finite-stage exactness passes to continuous cohomology

Author: Worker 21.

`Langlands.Continuous.finiteStageExactnessLimit` proves exactly the published
proposition `Langlands.Continuous.FiniteStageExactnessLimit.{u}`. It retains the
arbitrary common universe, commutative coefficient ring, compact locally compact
topological group, genuine discrete module, open normal subgroup, and natural
cohomology degree. The finite-stage injectivity and range–kernel equalities are
hypotheses of this generic proposition. The result does not supply these
hypotheses in the field-theoretic application and does not prove
`AbsoluteH2InflationExactness` by itself.

The implementation imports the published finite-quotient comparison proof,
subgroup refinement constructions, and restriction comparison proof. It proves
two elementwise consequences of the comparison isomorphism using Mathlib's
filtered module colimits: every continuous cohomology class has a representative
at an actual finite stage, and a finite-stage class whose continuous image is
zero becomes zero after refinement to a smaller open normal subgroup. The
second assertion compares that representative with zero in the filtered colimit;
the forgetful functor from modules preserves filtered colimits. These are the
lemmas `finiteStageToContinuous_jointly_surjective` and
`finiteStageToContinuous_eventually_zero`.

The auxiliary lemmas `finiteInflation_refl` and `finiteInflation_trans` recover
identity and composition of the actual inflation maps from functoriality of the
published finite-quotient diagram.

For injectivity at the specified subgroup `H`, take the difference of two classes
with equal continuous images. Eventual vanishing gives a stage contained in `H`
where its inflation is zero. The assumed finite-stage injectivity then makes the
difference zero.

For containment of the continuous inflation range in the restriction kernel,
apply the finite exactness hypothesis at `H` itself. Inflation along the identity
refinement is the identity, so restriction kills every class at that stage. The
published identity `finiteRestriction_comp_stage` transports the vanishing to
the actual continuous restriction map.

For the reverse containment, represent a continuous kernel class at an ambient
finite stage `N`. Restriction compatibility and eventual vanishing for the
restricted module give an open normal subgroup `P` of `H`, contained in the
restriction of `N`, where the restricted class is zero. The open subgroup `H` is
closed in the compact ambient group, hence compact; its compact topology also
supplies the local compactness needed by the comparison theorem. The published
`exists_ambient_openNormal` supplies an ambient open normal subgroup `M` lying
inside `H`, whose restriction lies in `P`. At `L = M ∩ N`, refinement compatibility
and composition of inflation show that the inflated representative has zero
finite restriction. Finite exactness at `L` gives a preimage from the stage `H`.
The identity `finiteStageToContinuous_refinement` then shows that this preimage
maps to the original continuous class.

All maps are the existing `finiteInflation`, `finiteRestriction`,
`finiteStageToContinuous`, and the topology-forgotten `continuousRestriction`.
There are no new hypotheses on the published statement and no proof holes or
new axioms. This is an internal proof of the published conditional limit lemma;
its provenance and connection with Serre's passage to the limit are documented
in `FiniteStageExactnessLimitStatement.md`. The implemented proof uses the
Library comparison isomorphism and Mathlib's filtered-colimit element criteria.
