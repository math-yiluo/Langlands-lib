# Stability of relative isogenies

`Langlands.GroupScheme.IsogenyStabilityStatement` is the conjunction of the
following assertions, in universe `u`.

1. For every scheme `S` and group scheme `G : Grp (Over S)`, its identity
   homomorphism satisfies `IsIsogeny`.
2. For every scheme `S`, group schemes `G`, `H`, `K` over `S`, and homomorphisms
   `f : G ⟶ H`, `g : H ⟶ K`, if both are isogenies, then `f ≫ g` is an isogeny.
3. For every pair of schemes `S`, `T`, every morphism `b : T ⟶ S`, and every
   isogeny `f : G ⟶ H` over `S`, the induced homomorphism
   `(Over.pullback b).mapGrp.map f` is an isogeny over `T`.

Here `IsIsogeny` is the published finite-flat-surjective predicate on the
underlying scheme morphism. The functor `Over.pullback b` is Mathlib's actual
pullback functor between the categories of schemes over these bases, and
`mapGrp` equips the pullbacks with their induced group structures and maps.
There is no restriction on `b`, and no field, noetherian, quasicompact,
smoothness, properness, or commutativity assumption. These assertions therefore
apply in particular to underlying homomorphisms of abelian schemes.

## Provenance

This is an internal consequence of the published definition in
`Langlands.AbelianScheme.Isogeny` and Mathlib's stability results for scheme
morphisms. It makes no new attribution to a literature theorem. The three
scheme predicates `IsFinite`, `Flat`, and `Surjective` contain identities and
are stable under composition and arbitrary base change. Their intersection
inherits those properties. Mathlib's
`CategoryTheory.MorphismProperty.overPullbackMap` expresses the resulting
base-change assertion on the underlying morphism of `Over.pullback`.

The Lean file defines the exact proposition; it does not prove it. The published
companion [IsogenyStability](IsogenyStability.md) proves this target as
`Langlands.GroupScheme.isogenyStability : IsogenyStabilityStatement.{u}`,
with no additional geometric hypotheses.
