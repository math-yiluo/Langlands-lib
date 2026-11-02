# Smooth sections of actual small-etale transport sheaves

This is an internal construction from the actual geometric section representation
in `EtaleTransportSections` and the established smooth-part adjunction. It adds no
new assertion attributed to Harris or Berkovich.

The inputs are a scheme `Y : Scheme.{u}`, a group `G : Type w` with a topology
making it a topological group, the established action convention
`ρ : G →* (Aut Y)ᵐᵒᵖ`, and a commutative ring `R : Type uR`. Module carriers lie
in `Type uM`. These four universes are independent, and no group-smallness
hypothesis is used here. The input sheaves are the actual module sheaves on the
labelled small-etale transport site. No continuity condition on their local
transport actions is imposed by this construction.

## The functor and its inclusion

`SmoothSections.sections` is the composite of `sectionRepresentation ρ R` with
`SmoothRep.smoothPartFunctor R G`. For a sheaf `F`, its underlying module is the
submodule of `F(Y)` consisting of the sections fixed by some open subgroup of
`G`. The action is the restriction of the action of the actual labelled
whole-scheme maps. Its explicit membership criterion is
`mem_smoothVectors_iff`:

- a section `s` belongs precisely when there is an open subgroup `H` such that,
  for every `g : H`, the linear map `F.obj.map (wholeMap ρ g).op` fixes `s`.

The criterion only needs a topology on `G`; invariance of this submodule under
all of `G`, and thus the smooth representation functor, uses the topological
group structure. On a sheaf morphism, the functor restricts its map on global
sections to these submodules. Additivity follows from the existing section and
smooth-part functors. Finite-limit preservation follows from finite-limit
preservation of the actual section representation and from the smooth part being
right adjoint to the inclusion of smooth representations.

`inclusion` is a natural transformation from these smooth sections, viewed as
algebraic representations, to `sectionRepresentation`. It is the smooth-part
adjunction counit whiskered by the geometric section functor. Its value on an
element is the subtype inclusion (`inclusion_app_apply`), hence each component
is a monomorphism (`inclusion_app_mono`).

For any smooth representation `A`, every intertwiner from its underlying
algebraic representation to the section representation of `F` has a factorization
`lift` through the smooth sections. `lift_inclusion` proves its composite with
the inclusion is the original map; `lift_unique` proves uniqueness by cancellation
against the monomorphism and faithfulness of the smooth representation inclusion.
These are the existing smooth-part universal property applied to actual sections.

`algebraicIsoOfSmooth` gives an isomorphism to all algebraic global sections when
that particular global-section action is smooth. Its homomorphism is exactly
`inclusion`. For a discrete topology every section is fixed by the open trivial
subgroup (`isSmooth_of_discreteTopology`); `discreteIso` packages the resulting
isomorphisms naturally in `F`. No smoothness hypothesis on all global sections
is assumed in the general construction.

## Strict complexes

For any index type `I : Type uI` and complex shape `c`, `complex` applies this
additive functor degreewise to an actual complex of transport module sheaves.
Its target is the category of complexes of smooth representations.
`complexIso` identifies it naturally with the algebraic section complex followed
by the existing `Langlands.Cohomology.smoothPartComplex` from
`DivisibleSystem.ScalarExtension`. This directly reuses the published degreewise
smooth-part construction.

`complexInclusion` is the natural chain map obtained by forgetting smoothness
and applying `inclusion` in each degree. `complexInclusion_f` identifies its
degree-`i` component with `inclusion` on `K.X i`; the proof reduces the functor
composition isomorphism to its identity component. Chain compatibility and
naturality come from mapping the section inclusion as a natural transformation
of additive functors.

## Scope

This pair constructs smooth global sections and strict complexes from actual
transport sheaves. The source is still the algebraic transport sheaf category;
it does not construct the full category of smooth equivariant etale sheaves.
Derived smooth sections, comparison with algebraic derived sections, compact
supports, supported Godement complexes, analytic uniformization, arithmetic
coefficient sheaves, level towers and the Harris specialization remain successor
obligations. In particular, no exactness of smoothing, preservation of
quasi-isomorphisms by degreewise smoothing, or identification of smooth
cohomology with the smooth part of ordinary cohomology is asserted here.
