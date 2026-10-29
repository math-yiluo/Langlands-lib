# Actual ideal-power quotient complexes of sheaf diagrams

Author: Worker 13.

This module constructs ideal-power reduction systems for actual complexes of
diagrams of module-valued sheaves. It uses the published sectionwise quotient
and sheafification functors, proves their additivity, and applies Mathlib's
prolongation of additive functors to homological complexes. The quotient chain
maps give a natural map into the ordinary inverse limit. Evaluation in a degree
and a diagram coordinate identifies this limit with the existing ordinary
sheaf-power limit and retains its genuine quotient maps.

## Inputs and conventions

The inputs are a category `C : Type uC` with morphisms in universe `vC`, a
Grothendieck topology `T` on `C`, a commutative ring `R : Type u`, an ideal
`I : Ideal R`, and the instance `HasSheafify T (ModuleCat.{v} R)`. The diagram
category `J : Type uJ` has morphisms in universe `vJ`. The complex shape is an
arbitrary `c : ComplexShape ι` with `ι : Type uι`. These seven universes are
independent. All diagrams and complexes use actual Mathlib sheaves and
natural-transformation or chain-map morphisms over this fixed site.

For a sheaf `F`, write `Q_n(F)` for the sheaf obtained by replacing each section
module `M` with `M / (I^n • ⊤)` and sheafifying. This notation refers to the
published `Langlands.Sheaf.AdicSystem.powers`, retaining the original
`R`-module structure. It is distinct from changing the coefficient ring to
`R / I^n`. The system is indexed by all of `ℕᵒᵖ`, including zero. For
`m ≤ n`, its transition is from exponent `n` to exponent `m`.

No particular scheme or étale site is required here. Any such site can be used
when it supplies the displayed sheafification instance. A fixed arbitrary
diagram category is retained throughout.

## Actual reductions and complexes

`Langlands.Sheaf.AdicSystem.powers_obj_additive` proves that each `Q_n`
preserves sums of sheaf morphisms. The proof unfolds it as the composite of
the additive inclusion into presheaves, pointwise application of the additive
module quotient, and additive sheafification. The module-quotient instance is
reused from `DiagramAdicComplex`; sheafification additivity is supplied by
pinned Mathlib `Sites.Abelian`.

`sheafDiagramPowers` applies `Q_n` and its transitions to each coordinate of a
diagram `J ⥤ Sheaf T (ModuleCat R)`. Its object functors are additive.
`sheafDiagramReductionFunctor` flips the two functor variables to package the
whole inverse system of a diagram.

`sheafDiagramComplexPowers` applies those additive functors to every term and
differential of a complex. Its transition chain maps come from prolonging the
natural transitions. The identity and composition equations for these
transitions are proved using the corresponding equations for natural
transformations. `sheafDiagramComplexReductionFunctor` packages the resulting
inverse system, functorially in the original complex.

The four component equations
`sheafDiagramComplexPowers_obj_X`, `sheafDiagramComplexPowers_obj_d`,
`sheafDiagramComplexPowers_transition_f` and
`sheafDiagramComplexPowers_map_f` identify the constructions explicitly. In
degree `i` and coordinate `j`, a reduced term is `Q_n((K.X i).obj j)`;
a differential is `Q_n.map ((K.d i k).app j)`; a transition is the actual
sheaf-power transition on that term; and a reduced chain-map component is
`Q_n.map ((f.f i).app j)`. Square-zero, the complex shape condition and
chain-map commutation are supplied by the additive-functor construction,
using preservation of zero and composition.

## Quotient maps and the ordinary limit

`sheafDiagramComplexPowerUnit` is the genuine quotient chain map at exponent
`n`, natural in the input complex. It prolongs the coordinatewise published
sheaf quotient map, using the canonical identity-complex isomorphism.
The underlying sheaf quotient map itself uses the inverse of the
sheafification counit followed by the sheafification of the sectionwise
module quotient. The theorem `sheafDiagramComplexPowerUnit_f` identifies
every degree and coordinate with exactly that map.

`sheafDiagramComplexPowerUnit_transition` proves compatibility with
higher-to-lower power transitions. The proof evaluates at a complex, degree
and coordinate and uses the existing sheaf quotient transition equation.
`sheafDiagramComplexPowerCone` therefore has the original complex as its
vertex and these actual quotient chain maps as its legs.

`sheafDiagramComplexPowerLimit` is the ordinary categorical inverse limit of
the constructed quotient complexes, functorial in the complex.
`sheafDiagramComplexPowerLimitUnit` is the universal lift of the quotient
cone. Its naturality is proved by comparing all limit projections and using
naturality of the quotient maps. The projection equation
`sheafDiagramComplexPowerLimitUnit_π` states that the unit followed by the
exponent-`n` projection is the quotient chain map.
`sheafDiagramComplexPowerLimitUnit_unique` proves that these projection
equations characterize the unit among all chain maps with the same source
and target.

The ordinary limits exist through Mathlib's module, sheaf, functor-category
and homological-complex limit constructions. In particular, the countable
inverse-system shape is small. No preservation of infinite limits by the
quotient or sheafification functors is an input.

## Evaluation and projection identities

`sheafDiagramComplexPowerLimitDegreeIso` identifies degree `i` of the complex
limit with the ordinary limit of the diagram-power system of `K.X i`.
It uses `preservesLimitIso` for `HomologicalComplex.eval`, whose preservation
instance comes from Mathlib's degreewise construction of complex limits.
`sheafDiagramComplexPowerLimitDegreeIso_hom_π` identifies its composite with
each ordinary projection with the degree component of the complex projection.

`sheafDiagramComplexPowerLimitEvaluationIso` then evaluates the diagram at
`j` and uses the canonical functor-category limit isomorphism. Its target is
the published
`Langlands.Sheaf.AdicSystem.inverseLimit T I ((K.X i).obj j)`.
The theorem
`sheafDiagramComplexPowerLimitEvaluationIso_hom_projection` identifies its
composite with each published sheaf projection with the corresponding
degree-and-coordinate component of the complex projection. Its proof uses
the degree projection identity and the functor-category projection identity.
Finally,
`sheafDiagramComplexPowerLimitUnit_evaluation_projection` proves that the
new unit, followed by this evaluation isomorphism and a sheaf projection,
is the genuine sheaf quotient map on `((K.X i).obj j)`.

## Provenance and scope

This is internal categorical infrastructure derived from the published actual
module and sheaf reductions in `Langlands.Coefficients.AdicSystem` and
`Langlands.Sheaf.AdicSystem`, the quotient-additivity instance in
`Langlands.Shimura.Coefficients.DiagramAdicComplex`, and pinned Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0. The relevant
Mathlib constructions are in `CategoryTheory.Sites.Abelian`,
`Algebra.Homology.Additive`, `Algebra.Homology.HomologicalComplexLimits`,
`CategoryTheory.Limits.Preserves.Limits` and
`CategoryTheory.Limits.FunctorCategory.Basic`. No new assertion from the
original literature is attributed to this internal unit.

The result concerns ordinary complexes and ordinary inverse limits. Exactness,
derived completion, cohomology comparison, comparison with associated
coefficient quotients, smooth or continuous actions, lisse-adic properties and
the Harris specialization remain separate obligations.
