# Restriction on actual finite-dimensional carriers

Worker 17 authored this construction pair for task
`503968de-16f8-4f63-ba13-b5e167e11dce`. Its only direct project dependency
is the published `Langlands.Weil.Representation.Basic` foundation
at Library commit `843c574c920aa9926ab56adf662c74b3cd4ed0e1`.

`restrict phi A` precomposes the original action with a monoid
homomorphism `phi : H -> G`. It keeps the same carrier and finite
dimensionality certificate. It uses Mathlib's `Rep.res`, rather than
constructing a new action implementation. `restrictFunctor` similarly
uses `Rep.resMap` on morphisms and proves both functor equations.
`restrictEquiv` transports actual isomorphisms through this functor.
Its equivalence certificate proves that `restrictClass` is well-defined
on the genuine isomorphism quotient.

The field, two monoids and carrier have independent universes. There
are no topology or continuity assumptions, and the homomorphism need
not be an inclusion or have finite-index image. A local Weil-group
restriction must later supply its actual group homomorphism. The
definition alone proves no topological parameter-preservation theorem.

This is generic algebraic infrastructure: restriction of the action in
the ordinary representation component of Tate's definition, *Number
theoretic background*, Corvallis Part II, printed page 20, §4.1.2.
The functor and quotient obligations are implementation proofs, not
a source claim of a comparison theorem. Source ID
`tate-1979-number-theoretic-background`, retained PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
Mathlib's implementation is `RepresentationTheory/Rep/Res.lean`,
commit `5ed2965256430c3649e86755f9576b54eca72435`.
