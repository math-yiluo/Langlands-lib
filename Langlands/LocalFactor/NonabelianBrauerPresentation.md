# Actual Brauer presentations and abelian evaluation

Worker 1727 supplies internal constructions for the existence argument on the
unchanged common-closure objects. A `Generator F E` consists of an actual finite
intermediate field `L` containing `E` and two continuous field quasicharacters.
`Presentation F E` is the free integer module on these data. No presentation is
chosen for an input class.

`generatorClass` induces the difference of the two actual reciprocal character
lines into the continuous exact Grothendieck group. Its actual virtual degree is
zero. `generatorClass_range` identifies its image with the published set of
character-difference induction generators, using the continuous abelianization
universal property and the supplied reciprocity equivalence. The theorem needs
no normalization property of that equivalence.

`virtualPresentation` extends these classes by integer linear combination. The
published `commonClosureDegreeZeroGeneration` identifies its range with the
actual dimension kernel. `presentationMap` restricts the codomain to that
kernel, and `presentationMap_surjective` proves surjectivity. Independent field
and representation universes are retained.

`HaarFamily` means a measure on every actual intermediate field, with no chosen
normalization. `generatorValue` uses precisely the epsilon ratio from
`Abelian.EpsilonUnit`, with the additive character pulled back by the actual
field trace. `evaluationMap` extends these values by integer linearity into
`Additive ℂˣ`: its additive zero is the complex unit one, addition is
multiplication of units, and integer multiplication is integer exponentiation.
The single-generator formulas expose both maps. The Haar-independence lemmas
apply the proved independence of actual abelian ratios generator by generator.

These are derived constructions, not a new arithmetic theorem from a source.
Their purpose is to give an explicit interface for the compatibility argument
in Deligne's 1973 local-constant construction, §4.2 and §4.7. No kernel
containment, well-defined evaluation on the actual quotient, or nonabelian
existence is asserted here. Surjectivity alone does not imply that a product of
abelian values is independent of a presentation.
