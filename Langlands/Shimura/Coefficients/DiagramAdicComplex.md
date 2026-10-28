# Actual power reductions and adic completion of coefficient complexes

Author: Worker 13.

Fix a commutative ring `R`, an ideal `I`, an actual group diagram
`D : J ⥤ GrpCat`, and an arbitrary `c : ComplexShape ι`. The coefficient-complex
constructions use ring, module-carrier and group-carrier universe `u`. The group
index object and morphism universes and the degree universe are independent.
The module additivity instances also allow the module universe to be independent
of the ring universe. No completeness or finiteness hypothesis is imposed.

The instances `Langlands.Coefficients.AdicSystem.powerReduction_additive` and
`completionFunctor_additive` prove that the published actual module quotient
and compatible-sequence completion functors preserve addition of morphisms.
Mathlib's `LinearMap.reduceModIdeal` and `AdicCompletion.map` are themselves
linear maps on the original morphism spaces. Their additivity, followed by
restriction of scalars, proves the two instances. The published
`EquivariantDiagram.mapFunctor_additive` then supplies additivity of the actual
diagram power and completion functors.

`coefficientComplexPowers I c` is an inverse system of endofunctors of
`HomologicalComplex (EquivariantDiagram D (ModuleCat R)) c`, indexed by all
natural numbers in the opposite order, including zero. It applies Mathlib's
`mapHomologicalComplex` to each actual diagram power functor and
`NatTrans.mapHomologicalComplex` to each actual power transition.
`coefficientComplexReductionFunctor` is its flip: it assigns the full inverse
system of quotient complexes to an input complex.

For a complex `K`, power `n` and degree `i`, the quotient term is the published
diagram reduction of `K.X i`. At group index `j` its underlying module is
`(K.X i).obj.obj j` modulo `I ^ n • ⊤`. Its differential is the reduction of
`K.d i k`, and a chain map is reduced degreewise. Thus square-zero and shape
conditions follow from the actual additive functor, while group actions and
group-index transitions are reduced by the existing diagram construction.
The three `coefficientComplexPowers_*` formulas record the degree objects,
differentials and chain-map components.

`coefficientComplexCompletion I c` applies the actual diagram completion functor
to every degree and differential. Its module at `(i,j)` is
`AdicCompletion I ((K.X i).obj.obj j)`, the module of compatible power-quotient
sequences. Its differential and chain-map components are the actual completion
maps of the originals; the three `coefficientComplexCompletion_*` formulas
record these facts. All actions and group-index transitions are completed by
the same coefficient functor.

`coefficientComplexPowerUnit`, `coefficientComplexCompletionUnit` and
`coefficientComplexCompletionProjection` are natural transformations whose
components are genuine chain maps. Their degree components are respectively
the original quotient map, canonical completion map and completion evaluation.
For the units the identity-complex isomorphism identifies the lift of the
identity functor with the actual identity functor. Evaluation after the
completion unit equals the quotient unit. Both the quotient units and
completion evaluations satisfy every power-transition equation. The proofs
evaluate the corresponding published diagram equations in each degree.

`coefficientComplexCompletionCone` has the completed complex as vertex and
the evaluation chain maps as legs. `coefficientComplexConeAt` evaluates an
arbitrary cone of quotient complexes in a fixed degree. The map
`coefficientComplexCompletionLift` uses the published actual diagram-completion
lift on these degree cones. To prove that these lifts commute with a
differential, the proof projects both composites to every power quotient,
uses naturality of completion evaluation, and applies the chain-map equation
for the original cone leg. The existing diagram-completion limit property
then makes the composites equal.

`coefficientComplexCompletionLift_projection` proves that the constructed lift
has exactly the prescribed legs. `coefficientComplexCompletionConeIsLimit`
proves the universal property of this same completion cone in the category
of complexes. Uniqueness is checked degreewise by the published diagram
completion limit property. Consequently this is an actual inverse limit of
quotient complexes, including its compatible actions and differentials.

The provenance is internal: the published `AdicSystem`,
`VaryingCoverReduction`, `DiagramCompletion` and
`EquivariantDiagramPreadditive` supply the actual module and diagram
constructions. Pinned Mathlib
`RingTheory/AdicCompletion/Functoriality.lean` and
`Algebra/Homology/Additive.lean` supply linearity and the actual complex lifting
constructions. No statement is attributed to Harris or Berkovich. This unit
constructs ordinary degreewise completion and its ordinary limit property.
It asserts no derived completion, exactness, commutation with cohomology,
associated-sheaf comparison, topology, smoothness or Harris-specific
identification.
