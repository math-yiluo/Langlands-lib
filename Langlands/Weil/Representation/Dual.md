# Algebraic duality on actual finite-dimensional carriers

Worker 17 authored this construction. `dual A` uses Mathlib's full
algebraic dual vector space and its inverse-element action:
`(r.dual g ell)(v) = ell(r(g⁻¹)v)`. Finiteness follows from Mathlib's
finite-dimensional dual instance. The output carrier universe is the
maximum of the coefficient and input carrier universes.

`dualFunctor` is a functor from the opposite category. It uses the
published `Langlands.dualIntertwining` on morphisms; its identity and
composition laws follow by evaluating functionals. `dualEquiv` uses the
published `Langlands.dualEquiv` and reverses the equivalence direction.
The inverse of this equivalence proves the compatibility required to
define `dualClass` on the genuine isomorphism quotient.

This is full algebraic duality; no smooth subspace or topological dual is
silently substituted. All finite ranks, including zero, are allowed.
There are no continuity or semisimplicity hypotheses.

Exact project dependency: Worker 0's
`Langlands.Representation.Dual.Definitions`, present at Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`.
Its effective Lean SHA-256 is
`53959e3b6cd0faad27f2566cbc9275fd537e5ab59d800f453bcbd61d05415ae5`.
This module imports that interface; it does not copy its implementation.
The finite-representation foundation `Langlands.Weil.Representation.Basic`
is published in that same Library tree.

Source correspondence: Casselman, *Chapter II. Smooth representations*
(June 16, 2019), printed page 6, §3, gives the inverse-element action on
the full algebraic dual and distinguishes it from the smooth
contragredient. Literature ID `casselman-2019-smooth-representations`,
PDF SHA-256
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
The finite-dimensional packaging, functor and quotient are intrinsic
implementation constructions, using Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
