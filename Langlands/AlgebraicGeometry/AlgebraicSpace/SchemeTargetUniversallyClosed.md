# Universal closedness after rebasing to a represented target

This internally derived unit compares the published universal-closedness
predicate for a morphism to a represented target scheme with universal
closedness of the actual rebased space's structural morphism. The comparison
has arbitrary scheme base, arbitrary represented target and arbitrary
algebraic-space source; no finiteness is required for this equivalence.

`SchemeTargetRebase.fibrePointsHomeomorph_snd` proves that the previously
constructed rebase fibre homeomorphism commutes with projection to the same
underlying test scheme, using the iterated-pullback projection formula and
the published fibre-restriction projection identity.
`testSchemePointsHomeomorph` compares an original test with its recovered
version over the represented target, by forgetting that new base and using
the canonical test isomorphism. `testFibrePointsHomeomorph` combines the rebase
fibre comparison, the equality of recovered tests, and the original-test
pullback isomorphism. Its projection lemma shows that these two homeomorphisms
form a commuting square on the actual quotient point spaces.

`SchemeTargetRebase.isUniversallyClosedMorphism_iff` uses this commuting square.
Forward preservation follows by scheme base change and the structural cartesian
square. For the converse, every original represented test is the Yoneda image
of a scheme map to the represented target. Universal closedness of the rebased
structural morphism supplies the closed map on its recovered test, and the
two homeomorphisms transport it to the original closed map.

`IsSeparatedMorphism.of_isPullback` proves cartesian preservation by applying
base-change stability to the relative closed-immersion diagonal property.
`SchemeTargetRebase.isSeparatedMorphism` applies the same argument after base
change to the target scheme. Under the stated affine and finite-presentation
atlas hypotheses, `SchemeTargetRebase.isProperMorphism` combines this
separatedness preservation and universal closedness with the published
finite-type and quasi-compactness reductions. It asserts preservation to the
rebased structural map, not reflection of properness in arbitrary cases.

`AffineTargetFamily.isUniversallyClosedMorphism_iff` combines the exact
surjective-etale target-atlas criterion with the rebase equivalence. Finally,
`AffineTargetFamily.isProperMorphism_structural` proves that a proper morphism
with the host finite-presentation atlases gives a proper structural family
over any affine target chart locally of finite presentation over the base.
Separatedness and universal closedness pass through the actual cartesian
square, and the actual family has the required finite-presentation atlas.
No etale or surjectivity hypothesis on that chart is needed for this forward
preservation statement.

The provenance is internal: the published actual target rebase and its fibre
homeomorphisms, scheme-base-change preservation, universal-closedness
cartesian preservation and target-atlas criterion, stability of relative
closed-immersion diagonals, and the finite-type atlas reductions. Integration
must follow `UniversallyClosedTargetAtlas`. The scheme-cover existence proof,
descent of a chosen cover, arbitrary-base-change family comparisons and the
full eight-property limit theorem remain separate obligations.
