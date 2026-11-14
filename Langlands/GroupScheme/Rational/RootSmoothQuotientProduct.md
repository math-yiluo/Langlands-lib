# Ordered root coordinates in smooth quotient kernels

This internal construction combines published smooth tangent-weight
transport, semigroup realization, and ordered products in smooth connected
unipotent groups. It provides an exact target chart with the same root
indices as a source chart, so membership in the kernel of a smooth
homomorphism can be tested separately in every ordered root coordinate.
The module does not assert the unconditional building opposite-factor
statement.

All declarations have arbitrary universe `u`. Let `k` be a field, let
`G` and `Q` be smooth affine group schemes over `k`, and let `S` be a
split torus over `k`. We use a homomorphism `i : S.toGrp ⟶ G` and a
homomorphism `q : G ⟶ Q` whose underlying scheme morphism is smooth.
Neither `i` nor `i ≫ q` is required to be a monomorphism, neither ambient
group is required to be connected, and surjectivity of `q` is not assumed.
Relative roots and relative root functors mean the Library's nonzero
conjugation weights and positive-multiple root functors for these maps.

`relativeRoots_comp_subset` proves
`relativeRoots (i ≫ q) ⊆ relativeRoots i`. Conjugation commutes with a
group homomorphism. The published smooth tangent-weight theorem
`actionWeightSpace_eq_bot_of_smooth` therefore implies that a weight space
vanishing in the source also vanishes in the target. The nonzero condition
on a relative root is preserved directly.

The remaining declarations use a cocharacter `ν` of `S` and an injective
enumeration `a : Fin n → characterLattice S` with range exactly
`indivisiblePositiveRoots i ν`. An explicit hypothesis requires the
positive cyclic tails of any two distinct roots in that set to be
disjoint. This is a retained root-combinatorics hypothesis; this module
does not prove it for arbitrary torus actions.

`exists_target_rootProduct` constructs a smooth connected unipotent
group scheme `U` representing the target dynamic unipotent functor for
`CommGroupScheme.groupHom ν ≫ i ≫ q`. It also constructs one group scheme
`H r` representing `subgroup (i ≫ q) (a r)` for every original source
index `r`, together with an isomorphism from the scheme product of all
`H r` to `U`. Composing this isomorphism with the inclusion of `U` in
`Q` is exactly the ordered multiplication of the root inclusions.
Source indices whose target root functor is trivial remain in the
product.

The implemented proof first realizes the positive semigroup subgroup of
`Q`. Its induced torus action has weight support equal to the positive
relative roots of `i ≫ q`, hence contained in the source positive roots
by the smooth weight inclusion. The source root-ray blocks partition that
larger support and satisfy the required disjointness and cross-exclusion
properties. The published
`hasOrderedSemigroupProducts_of_unipotent.for_larger_support` supplies
the ordered product with these same blocks. Transport through the closed
inclusion into `Q`, the root-ray closure identity, and cyclic-root
comparison identify every factor with the stated target root functor.
Positive-semigroup comparison identifies the represented group with the
dynamic unipotent functor without requiring connectedness of `Q`.

`TargetRootProductChart` packages the representing group, its inclusion,
the source-indexed target factors and their inclusions, the product
isomorphism, both representation properties, and the exact multiplication
identity. `targetRootProductChart` chooses such a package using the proved
existence theorem. It makes no canonicity or uniqueness claim.

`orderedPoints_comp_eq_one_iff` applies to any original representing
root factors `j r : H r ⟶ G`, any test scheme `T` over `k`, and any
tuple `x r : T ⟶ (H r).X`. It proves that the ordered product of the
original factors maps to the identity under `q` if and only if each
original coordinate maps to the identity under `j r ≫ q`. The proof
uses the published root maps from the original factors to the target
chart. Target ordered multiplication is a monomorphism, since it is the
composite of a scheme isomorphism with a representing inclusion.
Comparing the image tuple with the identity tuple forces every target
coordinate to be the identity. Conversely, multiplying identity images
gives the identity.

This is coordinate reflection for the full kernel of the supplied smooth
homomorphism on all test schemes. It imposes no connectedness or
unipotence assumption on that kernel. Specializing it to a reductive
residue quotient, transporting integral root charts to its special
fibre, and proving generation of an entire integral radical preimage
remain separate steps.
