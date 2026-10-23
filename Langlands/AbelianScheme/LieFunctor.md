# Functoriality of relative Lie modules

Let `S` be an arbitrary scheme and `f : G ⟶ H` an actual group-scheme
homomorphism over `S`. The module constructs the differential
`Langlands.GroupScheme.lieMap f : G.Lie ⟶ H.Lie` and proves its identity and
composition laws. No smoothness, commutativity, finite-presentation or
local-freeness hypothesis is needed.

## Construction and meaning

Write `e_G` and `e_H` for the identity sections, and `Ω_G` and `Ω_H` for the
relative differential sheaves over `S`. The identity-preservation equation
`e_G ≫ f = e_H` and the canonical composition isomorphism for module pullback
give `identityPullbackIso f`, an isomorphism of functors

`e_H^* ≅ e_G^* f^*`.

The notation on the right describes application order; in Lean this is
`pullback f.hom.hom.left ⋙ pullback G.identitySection`. The actual relative
differential morphism `relativeDifferentialsMap f.hom.hom.left f.hom.hom.w`
has source `f^* Ω_H` and target `Ω_G`. Its pullback along `e_G`, preceded by
the comparison, defines

`cotangentMap f : e_H^* Ω_H ⟶ e_G^* Ω_G`.

The Lie map is the internal `O_S`-module dual of this morphism, using
`Langlands.Scheme.Modules.dualMap`. It is therefore a morphism of the actual
module sheaves, not merely a map of global sections. The lemma `lieMap_eval`
states that, on every open `U`, the resulting functional evaluates on a
cotangent section `ω` by first applying `cotangentMap f` to `ω` and then
evaluating the original functional.

## Implemented proofs and functors

The private `sectionPullbackIso_comp` lemma proves the required pullback
comparison for any two composable maps preserving chosen sections. After
substitution of the section equalities, it applies Mathlib's
`Scheme.Modules.pseudofunctor_associativity` and cancels the canonical
isomorphisms. `identityPullbackIso_comp` specializes this argument to group
identities.

The proof of `cotangentMap_id` combines `relativeDifferentialsMap_id` with
`pseudofunctor_left_unitality`. The proof of `cotangentMap_comp` combines
`relativeDifferentialsMap_comp`, naturality of `identityPullbackIso`, and the
comparison just proved. Its order is contravariant:

`cotangentMap (f ≫ g) = cotangentMap g ≫ cotangentMap f`.

The two laws for `dualMap` then prove `lieMap_id` and `lieMap_comp`, with
covariant order:

`lieMap (f ≫ g) = lieMap f ≫ lieMap g`.

These proofs supply the fields of `Langlands.GroupScheme.lieFunctor S`.
The namespaces `Langlands.CommGroupScheme` and `Langlands.AbelianScheme`
each expose `lieMap`, `lieMap_id`, `lieMap_comp`, and `lieFunctor`, by
applying the same construction to their existing underlying group schemes.
Thus their objects are exactly the previously constructed `Lie` modules.

## Provenance and scope

This is a derived construction from the Lie object in
`Langlands.AbelianScheme.Lie`, the universal-derivation-induced differential
map and its proved laws in
`Langlands.AlgebraicGeometry.RelativeDifferentialsMapsCoherence`, and the
internal dual in `Langlands.AlgebraicGeometry.ModuleDual`. It introduces no
independent source definition and no assumed differential or functoriality
law. The comparison and composition proofs are categorical consequences of
these constructions and Mathlib's module pullback coherence.

Functoriality under composition does not establish additivity with respect
to the pointwise group law on homomorphisms. This module does not assert
that `lieFunctor` is additive, construct an endomorphism ring action or its
rational extension, or prove rank, local freeness, base change or a Lie
bracket. Those are separate mathematical obligations.
