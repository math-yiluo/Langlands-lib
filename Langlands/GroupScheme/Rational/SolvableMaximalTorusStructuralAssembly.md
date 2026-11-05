# Rational maximal-torus conjugacy with the stable-vector premise discharged

Worker 1333.

This internal companion to `SolvableMaximalTorusAssembly` uses the published
unconditional theorem
`RelativeRoot.splitUnipotentStableVectorSubgroup.{u}`. It supplies that theorem,
and the published `RelativeRoot.torusVectorActionLinearization.{u}`, to the
existing section and conjugacy constructions. It also uses the actual quotient
retained by `TorusGeneratedSplitGeometricRadicalQuotient`, so that the
finite-Galois route does not require a second quotient construction.

For a smooth connected affine actual group scheme `G` over any field `k`,
`SplitGeometricRadicalTorusQuotient.sectionHom` takes the existing data `D`:
an actual ground-field radical and inclusion, its geometric radical predicate,
its ground-field split-unipotent series, and an actual `SmoothNormalQuotient`
of that inclusion whose target is a torus. It returns an actual group-scheme
homomorphism from that stored quotient target to `G`, over the original field.
`sectionHom_comp` proves that its composite with the stored projection is the
identity of the same target.

The construction extracts smoothness, connectedness, closedness and unipotence
from the ground-field part of the geometric radical predicate. Closedness
supplies the required monomorphism. It then applies
`IsTorus.splitUnipotentExtensionSection` to the stored projection and its full
represented fppf kernel identity, with both structural inputs supplied by the
two published theorems. The companion identity is the specification of that
same chosen section.

`SplitGeometricRadicalTorusQuotient.maximalToriAreConjugate` applies the existing
`maximalToriAreConjugate_of_splitUnipotent_torus_section` to this section and
quotient. Its conclusion uses the unchanged `MaximalToriAreConjugate`, hence
gives an actual rational conjugating point and an actual isomorphism of the
source tori. This theorem has no structural premise beyond the supplied data.

Three companion theorems conclude the exact published
`SolvableMaximalTorusConjugacyStatement.{u}` with the following explicit inputs:

- `solvableMaximalTorusConjugacy_of_splitGeometricRadical_and_torusQuotient`
  takes `TorusGeneratedSplitGeometricRadicalStatement` and
  `SolvableTorusQuotientStatement`. It instantiates the earlier three-input
  assembly with the proved stable-vector theorem.
- `solvableMaximalTorusConjugacy_of_splitTorusDominatedQuotient` takes
  `SplitTorusDominatedSolvableQuotientStatement` and
  `UnipotentSplitTorusDominationStatement`. It chooses the smooth
  torus-generated envelope of the original group. Its published properties
  give smoothness, connectedness, affineness, solvability and ground-field
  torus generation. The retained-quotient constructor then supplies one set
  of radical and quotient data, using the two explicit inputs and the proved
  stable-vector theorem. The data's conjugacy theorem applies inside that
  envelope, and the envelope's conjugacy transport returns the original
  conclusion.
- `solvableMaximalTorusConjugacy_of_torusQuotient_and_dominationSplitness`
  takes `SolvableTorusQuotientStatement` and
  `UnipotentSplitTorusDominationStatement`. It supplies the published reduction
  `splitTorusDominatedSolvableQuotient_of_solvableTorusQuotient` to the preceding
  theorem. Thus no separate geometric-radical premise is required in this route.

Every field and characteristic, finite and imperfect fields, arbitrary
nonsplit maximal tori, and universe `u` are retained. All statement declarations
and geometric predicates are unchanged. The displayed pairs of structural
inputs remain hypotheses; this module does not prove them or the unconditional
host target. Its provenance is the explicit composition of the named Library
constructions, with no additional external assertion. It does not use either
maximal-split-torus conjugacy family.
