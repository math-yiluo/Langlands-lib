# Finite-index induction

Worker 17 authored this module. It constructs algebraic induction
on Mathlib's actual space of functions `f : G → A` satisfying
`f(s*g) = r(s)(f(g))`. The ambient group acts by right translation.
For finite index this is the usual induced representation; `induceIsoMathlib`
identifies it with Mathlib's tensor-and-coinvariant construction.

`Induction.coordinates` evaluates functions on chosen right-coset
representatives. Its explicitly constructed inverse uses the subgroup factor
`g * representative(g)^-1`. The inverse laws are proved from equivariance.
This linear equivalence proves finite dimension and the formula
`rank (induce S A) = S.index * rank A`. The representation itself does not depend
on a choice of representatives. These are used only in the coordinate proof.
`induceMap`, `induceFunctor`, `induceEquiv`, and `induceClass` supply actual maps,
functor laws, isomorphisms, and quotient well-definedness.

Source correspondence: Tate, *Number theoretic background*, Corvallis Part II,
printed pages 9–10, §2.1, introduces restriction and induction for the finite-index
Weil subgroup of a finite separable extension. Source ID
`tate-1979-number-theoretic-background`, retained Part II PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The equivariant-function realization and the finite-index comparison are the
implementation of that algebraic construction using pinned Mathlib
`RepresentationTheory.Coinduced` and `RepresentationTheory.FiniteIndex`
at commit `5ed2965256430c3649e86755f9576b54eca72435`.

This generic construction assumes a field and an actual finite-index subgroup.
It does not assert continuity or open inertia kernel. Those conditions and the
actual local-field subgroup specialization are separate obligations. General
representations are allowed, including rank zero, without irreducibility or
semisimplicity requirements. The carrier universe of the function model is the
maximum of the group and original carrier universes. The additional universe
constraint in `induceIsoMathlib` is inherited from the pinned comparison theorem
and does not restrict `induce`.

The only project import is the published
`Langlands.Weil.Representation.Basic` module, present at Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`. The paired
`InductionTopology` module in this contribution proves the open-kernel
certificates and constructs the open-inertia objects and classes. Neither
module imports pending Weil–Deligne definitions or other operation submissions.
