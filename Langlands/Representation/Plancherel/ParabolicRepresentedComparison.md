# The literal parabolic model and the represented Levi model

This internal derived adapter compares two existing formalizations of the
same objects. The first is the literal-subgroup model of the Plancherel
generic-irreducibility target: the Jacquet functor `jacquetFunctor h hU`
applied to the Levi-twisted induction
`DynamicNormalization.leviTwistedInductionFunctor h hU`, over the literal
Levi `parabolicLeviPointSubgroup p l`. The second is the represented-parabolic
model: `RepresentedParabolic.leviJacquetFunctor` applied to
`RepresentedParabolic.leviInductionFunctor`, over the Levi's own rational
points. Both models are existing Library definitions of normalized parabolic
induction, the normalized Jacquet module and its unitary selected-weight part.
This module only identifies them; it makes no new mathematical claim about
either and cites no external source.

## General transport

- `pullbackPullbackIso`: two successive pullbacks along topological group
  isomorphisms equal the pullback along any pointwise-equal composite, by the
  identity on vectors.
- `pullbackSubgroupCongrReflIso`: pullback along the identification of a
  subgroup with itself is the identity.
- `selectedWeightPart_comp_toSubmodule` and `selectedWeightPartCompEquiv`:
  for a smooth action of `K` and a topological group isomorphism `e : H ≃ K`,
  the selected generalized-weight part for a central map `j` into `H` of the
  pulled-back action has the same vectors as the selected part for `e ∘ j` of
  the original action. The proof uses the published smooth characterization
  of generalized weight spaces on both sides. The equivalence is the identity
  on vectors.
- `jacquetInductionSubgroupCongrIso`: equal parabolic, Levi and radical
  subgroups give the same normalized Jacquet module of normalized induction,
  after identifying the coefficient group. The proof substitutes the
  equalities.
- `intertwiningCompLinearEquiv`: changing the acting group along a
  topological group isomorphism is a linear equivalence of intertwiner
  spaces. The underlying linear maps do not change.
- `intertwiningPrecompLinearEquiv`: precomposition with the inverse of a
  representation equivalence is a linear equivalence of intertwiner spaces.
  The source carriers may lie in different universes.

## The actual comparison

The setting is that of the host target: a nonarchimedean local field, an
affine connected reductive `G` with canonical point topology, the actual maps
`p`, `l`, `a`, `n`, the compatible root presentation `pres`, the
geometric-radical witness `hn`, the literal semidirect decomposition `h` and
radical closedness `hU`.

- `parabolicRadical_isIso_subgroupMultiplication`: the presentation makes
  Levi-first multiplication `subgroupMultiplication l n` an isomorphism. The
  proof applies the published dynamic multiplication isomorphism to the
  presentation's equalities of the parabolic, Levi and radical with the
  dynamic subgroups of the split-component cocharacter. This is the
  represented model's structural input.
- `parabolicRepresentedJacquetInductionIso`: for every smooth `σ` of the
  literal Levi, pulling back the literal `J(I(σ))` along
  `parabolicLeviPointHomeomorph pres` gives a representation isomorphic to the
  represented Jacquet module of the represented induction of the pulled-back
  `σ`. The proof composes the following steps. The published
  `normalizedInductionLeviTwistIso` identifies the Levi-twisted induction with
  normalized induction. Its unimodularity input is the published
  `parabolicRadical_isUnimodular`. The literal subgroups equal the represented
  point images by `RepresentedParabolic.pointImage_eq_range_carrier`. The
  pullbacks are then reassociated along the represented Levi points
  equivalence.
- `parabolicSelectedJacquetHom_rank_eq_representedUnitary`: for every `τ`,
  consider intertwiners from the selected unitary part of the literal `J(I(σ))`
  into `τ`. Here the selected characters of the actual `A(F)` are those with
  normalized real part zero. Their cardinal rank equals the rank of
  intertwiners from `RepresentedParabolic.leviUnitaryJacquetModule` of the
  represented induction into the pulled-back `τ`. The linear equivalence
  first changes the acting group, then transports the selected part along the
  pullback. It then applies the existing `selectedWeightEquiv` to the
  isomorphism above. The last step is the existing
  `RepresentedParabolic.selectedLeviJacquetEquivUnitary`.
- `parabolicJacquetHom_rank_le_representedUnitary`: suppose the literal
  induction is admissible and `σ` satisfies the host's exact
  `IsSquareIntegrableModCentralSubgroup` predicate for the range of
  `parabolicSplitComponentPointHom pres`, with any quotient Haar measure.
  Then the rank of Hom from the whole literal `J(I(σ))` into `σ` is at most
  the rank of Hom from the represented unitary Jacquet module of the
  represented induction into the pulled-back `σ`. This combines
  `parabolicJacquetHom_rank_le_unitaryWeights`, from the companion
  `ParabolicJacquetUnitaryRestriction` module, with the equality above.

The admissibility of the literal induction stays an explicit hypothesis. This
module proves no bound on the represented unitary Hom space, no geometric
filtration and no irreducibility. Its purpose is to let a represented-model
bound on that unitary Hom space be applied to the literal target.
