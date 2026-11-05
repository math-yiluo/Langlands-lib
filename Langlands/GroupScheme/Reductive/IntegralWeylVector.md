# Integral Weyl vector

This internal construction starts with a supplied integral root datum `P`, a
base `b`, and the explicit hypothesis `hspan : P.corootSpan ℤ = ⊤`. The root,
weight and cocharacter index types may inhabit independent universes. It
constructs an integral weight `rho P b hspan` characterized by pairing to one
with every simple coroot. The lemma `eq_rho_of_pairing_simple` proves this
characterization is unique, and `eq_of_pairing_simple_eq` says that all weights
are determined by their values on simple coroots under the same spanning
hypothesis.

The proof uses Mathlib's `RootPairing.Base.span_coroot_support`: the simple
coroots span the same integral module as all coroots. Together with their
independence, the supplied full-span hypothesis therefore makes them an
integral basis, named `corootBasis`. The perfect pairing identifies the
functional taking the value one on each basis vector with an actual weight.
Basis extensionality proves uniqueness. This is an internal derivation from
these root-datum and linear-algebra interfaces; it does not import an external
highest-weight theorem.

For a finite root index type, `positiveRootSum P b` is the sum of the roots
positive for `b`. This module does not identify that sum with twice `rho`.
It does not construct a root datum, prove integral coroot generation from the
geometric definition of simple connectedness, extend the weight to a Borel,
or construct a representation. Those remain separate obligations in the
big-cell and Steinberg argument.
