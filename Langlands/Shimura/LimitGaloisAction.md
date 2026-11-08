# Decomposition groups and Frobenius on limits of Galois actions

This internal construction relates the decomposition-group notions of
`Langlands.Shimura.DecompositionGroupAction` to limits of Galois actions.
Let `R` be a commutative ring, `K` a number field and
`M : J ⥤ Action (ModuleCat R) (Field.absoluteGaloisGroup K)` a diagram of
Galois actions on `R`-modules. Suppose that `M` has a limit in the category
of actions and that the forgetful functor to `ModuleCat R` preserves it.
Then the limit is unramified at a finite place `v` when every vertex is, and
the projections of the limit intertwine the geometric Frobenius
endomorphisms at `v`. The declarations are in namespace
`Langlands.Shimura.LimitGaloisAction`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, §5 on printed p. 313, considers `λ`-adic representations of the
Galois group that are unramified at all but finitely many places, and
Theorem 5.7 characterizes them through Frobenius characteristic polynomials
(formula (5.6)). `λ`-adic cohomology is an inverse limit of cohomology with
torsion coefficients. This module shows that unramifiedness passes from the
torsion stages to the limit, and that the projections to the stages
intertwine the Frobenius endomorphisms. Nothing is proved about
unramifiedness of any particular diagram, and no relation between
characteristic polynomials of the limit and of the stages is stated.

## Inputs

- From the published `Langlands.Shimura.DecompositionGroupAction`:
  `localRestriction`, `atFinitePlace`, `IsUnramifiedAlong` (every element of
  the actual inertia subgroup acts trivially after restriction along a
  closure embedding `ι`), `IsUnramifiedAt` (along Mathlib's chosen
  embedding), `geometricFrobenius` and `geometricFrobenius_naturality`.
- From Mathlib: limits in `Action`, the forgetful functor `Action.forget`,
  `isLimitOfPreserves` and `IsLimit.hom_ext`.

## Declarations

Let `v : Global.FinitePlace K`, let `ι` be a closure embedding at `v`, and
assume `[HasLimit M]` and
`[PreservesLimit M (Action.forget (ModuleCat R) (Field.absoluteGaloisGroup K))]`.

- `isUnramifiedAlong_limit hM`: if every `M.obj j` is
  `IsUnramifiedAlong (ModuleCat R) v _ ι`, so is `limit M`.
- `isUnramifiedAt_limit hM`: if every `M.obj j` is `IsUnramifiedAt` at `v`,
  so is `limit M`.
- `geometricFrobenius_limit_π v M ι j`: the geometric Frobenius endomorphism
  of `limit M` at `v` along `ι`, followed by the projection
  `(limit.π M j).hom`, equals the projection followed by the geometric
  Frobenius endomorphism of `M.obj j`. This needs no preservation
  hypothesis.

## Proof outline

Let `i` be an element of the inertia subgroup. Since the forgetful functor
preserves the limit, two endomorphisms of the underlying module of the limit
are equal once they agree after every projection. The projection
`limit.π M j` is a morphism of actions, so composing the action of `i` on
the limit with it gives the projection followed by the action of `i` on
`M.obj j`. That action is the identity by hypothesis. The Frobenius
statement is `geometricFrobenius_naturality` for `limit.π M j`.

## Provenance

This is an internal construction on top of the published
`Langlands.Shimura.DecompositionGroupAction` and Mathlib's limits in
categories of actions. Harris (1999), §5 and Theorem 5.7 on printed p. 313,
is motivation only.
