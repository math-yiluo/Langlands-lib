# Direct normalized functors for a composed block parabolic

Authors: Worker 8, with Worker 14's inner-refinement functor pattern adapted
for the direct construction.

For an ordered block shape `B` and refinement `S`, the source of direct
induction is the actual subgroup `refinedLevi F.Carrier B S`, and the target
is the original matrix group `GL_n(F)`. Direct Jacquet goes in the reverse
direction. Both use the actual smaller matrix parabolic and full ambient
radical constructed in `RefinementComposition`.

## Quotient and action

`ComposedJacquetModule B S ρ` is the quotient of the original vector space
by the span of `ρ(u)v - v` for `u` in the full `composedUnipotent`. Its
canonical quotient map is `composedJacquetMk`. The actual embedded refined
Levi acts through `composedLeviNormalizer`, using the published normalizer
action on coinvariants. Thus the unnormalized action sends `[v]` to
`[ρ(B.leviEmbedding m.val)v]`. These constructions work over any
commutative ring as the matrix base ring, with complex representation
coefficients; smoothness additionally uses the topological-ring structure.

Over a finite extension `F` of `Q_p` with compatible topological data `T`,
`normalizedComposedJacquet` twists that action by the canonical inverse
half of `T.composedLeviModulus B S`. The implemented action formula is
`m [v] = δ_composed(m)^(-1/2) [ρ(B.leviEmbedding m.val)v]`.
An ambient intertwiner descends by `[v] ↦ [f(v)]`. Smoothness follows from
smoothness of the normalizer quotient action, continuous pullback along
the embedded Levi map, and the open kernel of the normalizing character.
The bundled functor's identity and composition laws are proved on
quotient representatives.

## Function space and action

`composedInducingRepresentation` inflates the original refined-Levi action
through `composedLeviProjection`, and twists by
`T.composedParabolicHalfModulus B S`. The direct induced space is the
published smooth function space from the actual composed matrix parabolic.
Its covariance is

`f(q g) = δ_composed(projection(q))^(1/2) σ(projection(q)) f(g)`.

The group acts by right translation, `(g f)(x) = f(x g)`, and every
induced function has an open uniform right stabilizer by construction.
The covariance and action formulas are proved from the actual function
space definitions. Induced intertwiners act by pointwise postcomposition;
the induced functor's laws reduce to pointwise equality. No support
condition is added here.

`T.normalizedComposedInductionFunctor B S` and
`T.normalizedComposedJacquetFunctor B S` use the canonical smooth categories
with the topology induced by `T`. The carrier universe of Jacquet is
unchanged. Induction has carrier universe `max uF uV`, where the field
universe `uF` and representation universe `uV` are independent. No
admissibility, finite-length, irreducibility or finite-dimensionality
assumption is imposed.

## Provenance and scope

The registered source is Bernstein and Zelevinsky, *Induced representations
of reductive p-adic groups I* (1977), ID
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Section 1.8, printed page 444 (PDF page 5), supplies positive-half
induction and inverse-half Jacquet conventions. Proposition 1.9(c),
printed page 445 (PDF page 6), and sections 2.1-2.3, printed page 446
(PDF page 7), motivate the composed triple for actual block refinements.
These are derived specializations of the published function spaces,
coinvariants, actual subgroup geometry and character constructions.

The definition implements smooth induction (the source's capital `I`).
Equality with compact induction for parabolics is a separate theorem.
This module asserts no functor transitivity, exactness, admissibility
preservation or Haar-scaling identification. In particular, the direct
functors are constructed from the actual full subgroup and radical,
without assuming an equivalence with iterated functors.
