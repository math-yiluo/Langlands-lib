# Geometrically equivariant coefficient inverse systems

This internal construction lifts the ordinary coefficient inverse systems from
`EtaleAdicTensorComparison` to the existing category of geometrically
equivariant etale module sheaves. It uses the actual scalar-extension and
scalar-restriction functors in `EtaleEquivariantScalarExtension`; it does not
postulate an action on a quotient or a comparison theorem.

## Scope and conventions

Let `X : Scheme.{u}`, let `R : Type u` be a commutative ring with an arbitrary
ideal `I`, and let `G : Type w` be a group. The scheme, coefficient ring and
module carriers use universe `u`; the group universe `w` is independent.
A homomorphism `ρ : G →* (Aut X)ᵐᵒᵖ` supplies the geometric action. The opposite
automorphism convention is the existing convention giving a left action after
contravariant translation. The sheaves are on the actual small etale site of
`X`.

For every natural number `n`, `equivariantPower I ρ n` is precisely scalar
extension along `R → R / I^n`, followed by restriction of scalars to `R`, in the
existing geometric-equivariant sheaf categories. Its underlying sheaf is
`extensionPower X I n`. The extension is tensoring sectionwise and sheafifying;
its action is the one already constructed from geometric pullback. All powers,
including zero, occur. In particular, the index zero has the zero quotient
coefficient ring.

## Why the ordinary transitions are equivariant

`extensionUnit_app_epi` proves that the underlying extension unit is an
epimorphism. Its composite with `extensionPowerIso` is the canonical sheaf
quotient map by `extensionPowerIso_unit`; that quotient map is epimorphic by
`Langlands.Sheaf.AdicSystem.quotientMap_app_epi`. The comparison is invertible,
so the extension unit is epimorphic as well.

For `m ≤ n`, `extensionTransition_comm` proves the equivariance equation for
the already constructed ordinary map `extensionTransition X I h`. The proof
precomposes both sides with the translated unit at level `n`. Translation is
the functor of the actual sheaf equivalence induced by the scheme
automorphism, so it preserves epimorphisms and this precomposition can be
cancelled. After precomposition, the two sides agree by equivariance of the
extension units and the proved ordinary transition-unit identity. Thus no new
transition map or equivariance hypothesis is supplied by the caller.

## Inverse system and canonical cone

`equivariantTransition` bundles the ordinary transition as an equivariant
morphism, naturally in the input equivariant sheaf. Its underlying map is
recorded by `equivariantTransition_app_hom`. The identity, composition and unit
laws are proved by forgetting equivariance and applying the ordinary laws;
equality of underlying maps determines an equivariant morphism.

`equivariantPowers` is the functor from `ℕᵒᵖ` to endofunctors of the equivariant
sheaf category. An inequality `m ≤ n` yields a map from level `n` to level `m`.
`equivariantFunctor` flips the arguments, giving an inverse system functorially
for each equivariant sheaf `F`. `equivariantQuotientCone` has vertex `F` and the
existing equivariant extension units as its legs. Its naturality is the proved
transition-unit law.

## Comparison after forgetting the action

`equivariantExtensionForgetIso` identifies the underlying entire inverse
system with `extensionFunctor X I`. It is the identity comparison: both the
objects and transition maps have precisely the existing ordinary definitions.
Composing with `extensionFunctorIso` gives `equivariantFunctorForgetIso`, a
natural isomorphism with the existing sheaf quotient-system functor
`EtaleAdicSystem.functor X I` after forgetting the input action. This compares
the whole inverse system, including naturality in the coefficient sheaf and
in the power index. `equivariantFunctorForgetIso_unit` additionally identifies
each canonical cone leg with the existing sheaf quotient map under that
comparison.

This constructs ordinary inverse systems with geometric equivariance. It
places no topology on `G` and asserts no continuity or smoothness. It does not
assert exactness of coefficient extension, preservation of injectives, an
identification with an adic completion, commutation with cohomology, or a
derived inverse-limit theorem. Specializing to the actual Harris coefficient
sheaves and proving the required smoothness and cohomological comparisons
remain separate obligations. The complex inverse-limit and Godement work has
separate ownership and is not replaced by this construction.
