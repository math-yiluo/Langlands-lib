# Reductivity of finite flat normal quotients

`Langlands.GroupScheme.reductiveFiniteNormalSubgroupQuotient` constructs the
actual reductive quotient of a reductive group scheme `G` over an affine
scheme `S`. The subgroup is specified by a homomorphism `i : N ⟶ G` whose
underlying morphism in `Over S` is monomorphic. The structure morphism of `N`
must be finite, flat and locally of finite presentation, and the full range
subgroup functor of `i` must be normal.

The result, `ReductiveFiniteNormalSubgroupQuotient i`, extends
`FiniteNormalSubgroupQuotient i`. It retains the actual quotient group
scheme, projection from `G`, affineness of the quotient over `S`, finiteness
of the projection, and
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) projection`.
The additional field `reductive` proves reductivity of the actual quotient.
The fppf quotient condition supplies flatness, scheme surjectivity and local
finite presentation of the projection and equality of its full kernel
range with the range of `i`. In particular, the projection is an isogeny
under the Library's finite, flat and surjective convention.

The construction is internal, derived from the affine quotient construction
`finiteNormalSubgroupQuotient` and the two preservation theorems proved in
this module. It imposes no centrality or smoothness assumption on the
subgroup. All declarations are polymorphic in the universe of `S`.

The first preservation theorem,
`isConnectedReductive_of_isIsogeny`, treats an affine target `Q` over a
field. Its hypotheses are connected reductivity of `G`, an isogeny
`q : G ⟶ Q`, and local finite presentation of the underlying morphism of
`q`. Smoothness of `Q` follows from
`smooth_target_of_surjective_flat_hom`; connectedness follows from the
surjective continuous map from `G`.

For geometric reductivity, the proof base changes the specified `q` to an
algebraic closure. The kernel pullback square makes its actual kernel
finite over that algebraic closure.
`finiteGroupSchemeUniformExponent`, in
`Langlands.GroupScheme.FiniteUniformExponent`, supplies a positive integer
that kills every point of this kernel on every test scheme. That theorem
applies to finite group schemes without a commutativity assumption.
The geometric core
`FiniteCentralQuotient.hasTrivialUnipotentRadical_of_kernel_pow_eq_one`,
in `Langlands.GroupScheme.Reductive.CentralFiniteQuotientReductive`, now
gives triviality of the target's geometric unipotent radical. The core
requires the uniform kernel exponent, flatness, local finite presentation,
and the source's trivial radical; it does not require centrality.

The second preservation theorem, `isReductive_of_isIsogeny`, works over an
arbitrary scheme `S`. It assumes a reductive source, an affine target,
and an isogeny locally of finite presentation. Flatness of the target
structure morphism descends along `q` by
`AlgebraicSpace.flat_of_surjective_flat_comp`; local finite presentation
descends by `locallyOfFinitePresentation_of_surjective_flat_comp`.
Base change of the actual `q`, the source field-fibre theorem from
`Langlands.GroupScheme.Reductive.BaseChange`, and the first preservation
theorem prove connected reductivity of every field-valued fibre of `Q`.
Mathlib's `Smooth.of_smooth_fiberToSpecResidueField` then proves smoothness
over `S`. Applying the same field result at the specified geometric points
supplies the geometric-fibre condition in `IsReductive Q`.

Finally, `reductiveFiniteNormalSubgroupQuotient` takes the actual quotient
from `finiteNormalSubgroupQuotient`, extracts its finite fppf projection,
and applies `isReductive_of_isIsogeny`. This helper does not construct the
finite flat normal part of a fibrewise isogeny's kernel over a Henselian
DVR. That kernel-part construction and the remaining global reductions
are still needed for `ReductiveFibrewiseIsogenyStatement`.
