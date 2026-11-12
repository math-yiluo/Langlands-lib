# Formal implications in the Bernstein block characterization

Worker 137. Supporting reduction for Task 5352, not an unconditional proof of its target.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version of 9 July 2026, source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, VI.7.2 Proposition and proof, printed pp.184–185 / PDF pp.190–191.

These derived helpers prove that the actual Jacquet-exclusion condition (iii) passes to subquotients and arbitrary actual direct sums. Compact containment of the standard radicals supplies exactness, and the published normalized Jacquet colimit-preservation theorem supplies the coproduct comparison. Irreducible constituents of a direct sum occur in a summand.

The module then proves that (iii) implies membership in the original saturated Bernstein block, conditional on the two already published support targets `BernsteinCuspidalSupportExistenceStatement` and `BernsteinInductionJacquetSupportComparisonStatement`. For an irreducible constituent of `V`, choose an actual cuspidal support and pass to a datum in the same inertial class occurring in its Jacquet module. Exactness places that datum in the Jacquet module of `V`; exclusion forces the datum to be related to the prescribed class. The published quotient criterion then gives block membership.

The two remaining source steps are named separately: `BernsteinFixedLeviBlockEmbedding` is the fixed-Levi embedding of a block object obtained in the source from the I/R embedding and its inertia components; `BernsteinInducedInertiaJacquetExclusion` is the geometric-lemma exclusion for induction of an arbitrary object in a single same-Levi inertia block. Neither target is proved here. Their predicates use the actual published standard-family objects, full rational inertia blocks, and saturated carriers and index universe `max uF uV`.

The theorem `bernsteinInduction_inertiaBlock_mem_saturatedBlock` combines geometric exclusion with the two support comparison targets to supply the induction-block membership bridge shared with the Bernstein decomposition proof. It remains conditional on all three inputs; no use is made of VI.7.3, which the source proves from this characterization.

The actual construction `bernsteinInertiaInducedSum` is a direct sum of normalized inductions from the chosen datum's standard Levi. `BernsteinInertiaInducedEmbedding` and `BernsteinInertiaInducedSubquotient` are exactly the published conditions (i) and (ii), with the same witnesses. The elementary implication (i) -> (ii) keeps those witnesses unchanged. Geometric exclusion, closure under direct sums and closure under subquotients give (ii) -> (iii).

`bernsteinBlockCharacterization_of_inputs` combines these implications and (iii) -> block with the supplied fixed-Levi embedding, proving the three equivalences for each datum and object. `BernsteinBlockCharacterizationPrerequisites` universally quantifies the four genuine inputs over the unchanged target setting. `bernsteinBlockCharacterization_of_prerequisites` has conclusion exactly `BernsteinBlockCharacterizationStatement.{uF,uV}` and retains that prerequisites proposition as an explicit hypothesis. This is a conditional supporting theorem, not the unconditional theorem required to complete Task 5352. No target/import file is modified, no missing statement is assumed as an instance, and no new axiom is introduced.

## Name of the file-local topology

The file-local instance `TopologicalSpace (rationalPoints G)`, the canonical point topology, is named `instBernsteinBlockCharacterizationReductionTopology`. It used to be anonymous. Because the imported `BernsteinJacquetInertiaExclusion` already held the base name, Lean gave it the generated name `Langlands.CuspidalSupport.instTopologicalSpaceRationalPoints_1`. `RationalUniversalSmallProgeneratorStatement` declares its own anonymous topology on rational points, with a different type, under the same generated name. Neither module imports the other, so any module that imports both failed with a duplicate-declaration error. `BernsteinJacquetInertiaExclusion` now names its instance explicitly as well. Without an explicit name here, this instance would take the freed base name, which `RationalUniversalProgenerator` also uses. Only the name changed: the type and value are as before, and no file refers to the instance by name.

Integration also gives the local affine, closed-immersion, finite-type and
Levi point-topology instances explicit module-specific names. Their types,
bodies and local scope are preserved; no consumer refers to their former
automatically generated names.
