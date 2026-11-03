# Kernels and annihilation of an actual derived subgroup

This internal helper works over every base scheme `S` in an arbitrary universe
`u`. It uses the published actual group objects, kernels and scheme-theoretic
derived-subgroup intersection. Its provenance is the following direct argument
from those definitions; it adds no structural assumption about reductive groups.

`SubgroupFunctor.kernel f` constructs the pointwise kernel subgroup functor of
any group-scheme homomorphism `f : G ⟶ H`. On each test scheme `T`, it is the
kernel of the induced homomorphism on `T`-points; restriction stability follows
by associativity and the preservation of the identity under restriction.
`mem_kernel` unfolds membership, and `range_kernelι` identifies this functor
with the full range of the actual kernel inclusion.

The imported `Langlands.GroupScheme.mem_range_kernelι_iff` from
`CentralIsogeny/Basic` identifies membership in the full range
functor of the actual kernel inclusion with having identity image. Its proof
uses the existing natural multiplicative equivalence `kernelPointsEquiv` and its
inverse, so the assertion concerns every test scheme over `S`, including
nonreduced test schemes.

For a homomorphism `f : G ⟶ H` to a commutative group scheme, the image of every
commutator is the identity. Thus its kernel range contains all commutators. If
`H` is separated over `S`, the existing kernel inclusion is a closed immersion.
The published minimality of `derivedSubgroup G` then gives
`derivedSubgroup_le_range_kernelι`: the derived subgroup functor is contained in
this kernel range.

For any actual inclusion `d : D ⟶ G` satisfying `IsDerivedSubgroup d`, its range
is the published derived subgroup functor. Applying the containment to every
point of `D` and using the existing extensionality theorem for group-scheme
morphisms proves `IsDerivedSubgroup.comp_eq_one`, namely `d ≫ f = 1`.
Specialization to the separated commutative multiplicative group gives
`IsDerivedSubgroup.characterRestrict_eq_zero` in the Library's additive character
notation.

No field, affineness, finite type, smoothness, connectedness or reductivity
hypothesis is needed. The general morphism lemma requires exactly commutativity
and separatedness of its target. These hypotheses are automatic for the
multiplicative-group target in the character lemma.

This unit does not construct a representing derived subgroup. Its morphisms
are defined over the same base as `d`. In particular it does not prove
`DerivedCommutativeAnnihilationStatement` or
`DerivedCharacterAnnihilationStatement`, which quantify new morphisms after
arbitrary algebra scalar extension without assuming the corresponding
base-change compatibility of the derived subgroup.

Authorship: Worker 1306.
