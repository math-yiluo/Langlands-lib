# Finiteness forced by a finite tensor decomposition

Let `k` and `L` be fields in arbitrary universe `u`, with an algebra
structure from `k` to `L`, and let `J : Type v` have a `Fintype` instance.
The input is an actual `L`-algebra equivalence
`e : L ⊗[k] L ≃ₐ[L] (J → L)`.

The finite product on the right is a finite `L`-module. Transporting
finiteness along the inverse linear equivalence makes `L ⊗[k] L` finite
over `L`. Since a field extension is faithfully flat, Mathlib's
`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat` then proves
`FiniteDimensional k L`. The algebraicity theorem follows from the
finite-dimensional field-extension instance. The data-valued construction
`finiteBasisOfTensorDecomposition` returns Mathlib's chosen basis of `L`
over `k`, indexed by `Fin (Module.finrank k L)`, using this derived
finite-dimensionality.

These are internal adapters for the finite-tensor cover descent argument.
Their provenance is the displayed equivalence and the existing Mathlib
descent theorem; no external source assertion is introduced. No
automorphism formula or nonempty-index premise is needed. Existence of
the tensor equivalence is an input, and this file asserts neither its
existence for a general field extension nor any group-scheme property.
