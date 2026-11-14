# Coordinates for an index-two pair of fixed fields

This is an internal field-theory helper for the quasi-split root-generation
argument. Let `k` and `K` be fields, with an algebra structure, and let
`H ≤ H'` be subgroups of the actual group `K ≃ₐ[k] K`. Assume
`H.relIndex H' = 2` and choose `σ ∈ H'` outside `H`. Write
`E = IntermediateField.fixedField H` and
`F = IntermediateField.fixedField H'`.

Index two makes `H` normal in `H'` and gives `σ² ∈ H`. Consequently
`apply_mem` shows that `σ` preserves `E`, and `apply_apply` shows that
its restriction is an involution. The definition `conjugation` is that
actual restriction, as a `k`-algebra automorphism of `E`.
`mem_lower_iff` identifies membership in `F` with membership in `E`
and fixedness by `σ`. These conclusions do not require finiteness or
Galoisness of `K/k`.

The next two results assume `FiniteDimensional k K`.
`exists_add_conjugate_ne_zero` produces `e ∈ E` for which
`e + σ(e) ≠ 0`. If every such sum were zero, its value at one would
make negation equal to the identity, so `σ` would fix every element of
`E`. The finite-extension fixed-field correspondence would then put
`σ` in `H`, a contradiction.

`exists_sub_conjugate_eq` proves that every `r ∈ E` satisfying
`σ(r) = -r` has the form `w - σ(w)` for `w ∈ E`. The implemented
choice is `w = r * σ(e) / (e + σ(e))`. In particular the proof also
applies in characteristic two.

Without a finiteness hypothesis, for `w ∈ E` outside `F`, `exists_linear_combination` writes each
`x ∈ E` as `a * w + b`, with `a, b ∈ F`. It takes
`a = (x - σ(x)) / (w - σ(w))` and `b = x - a * w` and checks
fixedness directly. The denominator is nonzero because `w ∉ F`.
`unit_decomposition` packages the nonzero case in the ambient unit
group `Kˣ`: there is a unit `a` whose value belongs to `F` such that
`x = a` or `x = a * (w + b)` for some `b ∈ F`. It follows by
splitting on the first linear coefficient and dividing the constant
coefficient by it in the nonzero case.

The provenance is internal: elementary subgroup-index facts and the
finite-extension fixed-field correspondence from Mathlib, followed by
the displayed field identities. No root-group or normalizer assertion
is included, and no restriction on the characteristic is imposed.
