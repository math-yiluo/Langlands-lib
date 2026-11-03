# Actual adelic norm-one maps from derived-subgroup containment

This internal unit connects the published scheme-theoretic derived subgroup
functor to the existing actual norm-one adelic group and ordered Siegel products.
It works over every number field F. Its basic map construction needs no
smoothness, affineness, finite type, connectedness, reductivity or
representability of the derived functor. All group-scheme morphisms and rational
characters in its hypotheses are over the same base Spec F.

For any actual morphism f : H → G, the hypothesis
`SubgroupFunctor.range f ≤ derivedSubgroup G` is containment on every test scheme
over Spec F. The published `Derived.KernelAnnihilation` module proves that every
morphism from G to a separated commutative group annihilates this derived
functor. In `charactersTrivialAlong_of_range_le_derived`, the target is the actual
multiplicative group. Its separatedness follows from the Spec construction and
base change. Each image point under f therefore belongs to the actual kernel
of every ambient rational character. The existing all-test morphism
extensionality theorem gives f followed by that character equal to the identity
character. This supplies exactly `AdelicGroupPoints.CharactersTrivialAlong`;
the identity is multiplicative notation for the zero rational character.

`range_le_normOne_of_range_le_derived` applies the existing
`range_le_normOne_of_charactersTrivialAlong` to obtain containment of the full
actual adelic image of f in `normOneSubgroup F G`. The latter is the intersection
of all normalized rational-character norm kernels. No restriction to positive
points or principal points is used in this conclusion. The specialization
`range_le_normOne_of_isDerivedSubgroup` applies to an actual derived inclusion
by its all-test range equality.

`mapToNormOneOfDerived` is the resulting continuous homomorphism from the full
`AdelicGroupPoints F H` into `normOneSubgroup F G`. Its underlying ambient map
is exactly the existing `AdelicGroupPoints.map F H G f`, as its value theorem
records. Continuity follows by restricting that continuous map to the inherited
subgroup topology. `mapToNormOneOfDerived_rational` proves the actual
principal-point formula: applying this map to the principal point attached to
x in H(F) gives `rationalNormOne F G` of the actual f-image of x. Subtype
extensionality reduces it to the imported rational naturality identity.

For any commutative group schemes T₀ and T, with actual morphisms j : T₀ → T
and i : T → G, `positiveMap_mem_normOne_of_range_le_derived` specializes the
full-range containment to the existing intrinsic positive subgroup of T₀.
The hypothesis is containment of the all-test range of the actual composite
j followed by i in the derived functor of G. `positiveMapNormOneOfDerived`
then restricts the existing continuous `positiveMap` to ambient norm-one
points, with exactly the original value formula. No split-torus presentation,
maximality, injectivity or nonzero rank hypothesis is required.

Finally `productSet_subset_normOne_of_derived` applies to the existing
`StandardFactorData D` and `CompactFactors C`, for an affine structure morphism
of G and any cocharacter used by that data. If the actual unipotent inclusion
and the actual composite T₀ → T → G both have all-test range in the derived
functor, every point of the existing ordered product ΩN ΩM A K lies in ambient
norm-one points, for every subset A of the intrinsic positive torus. The proof
derives both character-triviality hypotheses and applies the published
`productSet_subset_normOne`. That theorem maps the norm-one Levi factor into
ambient norm-one points by functoriality and treats the supplied compact subgroup
by the proved compact-character argument. Thus no extra condition on these two
factors is needed. Both weak and strict chamber products are instances of this
arbitrary-subset conclusion.

The provenance is the published `AdelicSiegelFactors`,
`AdelicGroupNormOneFunctorial` and `GroupScheme.Derived.KernelAnnihilation`
constructions and their intrinsic laws, imported by Lean module. The module
adds no external structural theorem. In particular it does not prove that the
standard unipotent or a maximal split torus has the required derived containment,
construct a representing derived subgroup, identify a minimal parabolic, or
establish Siegel coverage, finite volume or analytic Haar unimodularity. It does
not assert the arbitrary-scalar-extension annihilation statements in
`GroupScheme.Derived.AnnihilationStatement`: its ambient characters are defined
over the original base, and evaluation on the actual adele algebra is handled
by the existing character-norm map.

Authorship: Worker 112.
