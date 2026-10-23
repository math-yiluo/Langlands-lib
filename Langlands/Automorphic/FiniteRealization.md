# Finite adelic realizations inside automorphic forms

This module constructs invariant spaces and faithful realization maps using the
actual `AutomorphicForms F n` of `Forms.lean`. It also relates an injective
equivariant map to the invariant image it determines. This is internal
construction infrastructure for the finite adelic action.

## Parameters and concrete carriers

The arithmetic field `F : Type uF` is a number field; `n : ℕ` is unrestricted.
Coefficients are `ℂ`. An external representation carrier used in the image
construction has an independent universe `uV`, an additive commutative group
structure and a complex module structure. No topology or finite dimension on
the vector spaces is required.

`FiniteRealization F n` is the type of subrepresentations of the existing
`automorphicFiniteRightAction F n`. Thus an element `S` specifies an actual
invariant subspace of the form space, including its position there.
`S.Space` is that subspace's carrier and `S.representation` is restriction of
the existing finite adelic action. Zero and reducible subspaces are permitted.
The optional predicate `S.IsIrreducible` is Mathlib's irreducibility of this
restricted representation, including nonzeroness.

`S.inclusion` is the injective intertwiner into `AutomorphicForms F n`.
`S.toContinuous` composes it with the published injective map into continuous
rational-invariant adelic functions, and is proved injective. The evaluation
formula is the existing positive right-translation convention:

`(representation(d) f)(x) = f(x * ofFinite(d))`.

Smoothness of `S.representation` is proved by transfer along its injective
inclusion into the smooth finite adelic form action. It is not an additional
field of realization data.

`S.localRepresentation v` restricts this action along the actual
identity-supported local insertion at a finite place. It is smooth by
continuity of that insertion, and its evaluation formula is right translation
by `ofFinite(localInclusion(v,g))`. Its carrier is still the whole space
`S.Space`; this construction does not identify it with an irreducible local
tensor factor.

## Realizations and representation classes

`S.smoothRepresentation` bundles the constructed action and proved smoothness
in the existing `Langlands.SmoothRep` category. `S.isoClass` uses that category's
existing quotient by isomorphism, at carrier universe `uF`. It forgets the
embedding into forms.

`isoClass_eq_iff` proves that two such classes are equal exactly when their
finite adelic representations admit an equivariant linear equivalence. It does
not assert that the actual form subspaces are equal or that their inclusions
agree. The proof converts between categorical isomorphisms and
`Representation.Equiv` using the existing category API.

`S.HasCentralCharacter χ` means containment in the published automorphic
subspace for the continuous idele-class character `χ`. The evaluation theorem
gives its prescribed scalar law on the actual functions. Under the explicit
instance `[CompactSpace (AdeleQuotient F)]`, `S.IsCuspidal` means containment in
the published cusp-form subspace. `constantTerm_eq_zero` proves vanishing of
every specified proper two-block constant term of a vector in `S`.
These properties concern the embedded space. This module does not descend
them to the quotient of finite representation classes.

## Constructed cyclic realizations

`generatedFiniteRealization F n f` is the span of the actual finite adelic
orbit of a given automorphic form `f`. It reuses
`FiniteVectors.orbitSubrepresentation`, with no assumption that this span is
finite-dimensional.

The module proves that it contains `f`, is the smallest finite invariant form
space containing `f`, and is nonzero whenever `f` is nonzero. The minimality
property also proves that the generated space has a prescribed central
character exactly when `f` belongs to that character subspace, and is cuspidal
exactly when the underlying function of `f` is cuspidal. No nonzero
automorphic or cusp form is asserted to exist.

## Equivariant images

`FiniteRealizationMap F n ρ` names the type of equivariant maps into actual
forms, and `FiniteRealizationMap.IsInjective F n T` abbreviates ordinary
function injectivity. `FiniteRealization.Equivalence F n S ρ` abbreviates a
representation equivalence from the model `ρ` to `S.representation`.
These names keep signatures compact without adding hypotheses.

For any complex representation `ρ` of the actual finite adelic group and an
intertwiner `T` from `ρ` to `automorphicFiniteRightAction F n`,
`finiteRealizationImage F n T` is Mathlib's invariant range of `T`. This is
constructed whether or not `T` is injective.

When `T` is injective, `finiteRealizationImageEquiv` constructs a
`Representation.Equiv` from `ρ` onto this actual image. Its underlying linear
equivalence is `LinearEquiv.ofInjective T.toLinearMap`; its equivariance follows
from the intertwining identity for `T`. Composition with the image inclusion is
proved to recover `T` exactly.

`HasFiniteRealization F n ρ` is the proposition that an injective such `T`
exists. `hasFiniteRealization_iff` proves that this is equivalent to existence
of an actual `FiniteRealization F n` whose action is equivalent to `ρ`.
The forward proof takes the range and the constructed image equivalence.
The reverse proof composes an equivalence with the faithful subspace
inclusion. Neither direction supplies an embedding for an arbitrary
representation.

## Provenance and remaining scope

All constructions derive from published Library objects: actual forms and
their finite/local actions, character and cusp subspaces, orbit spans,
smoothness transfer, and the smooth representation category. The only
additional algebraic mechanism is Mathlib's equivalence of an injective
linear map with its range, bundled with its proved intertwining identity.
No new claim from external literature is introduced.

Finite invariance does not require stability under archimedean
differentiation or the infinite compact group. These objects are therefore
finite adelic realizations, not the full automorphic representation category.
Admissibility, occurrence of irreducible representations, automorphic
factorization, uniqueness of local components, and isobaric classification
remain separate obligations. A finite local restriction retains any
complementary multiplicity space.
