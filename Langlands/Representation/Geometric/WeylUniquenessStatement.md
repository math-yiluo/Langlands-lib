# Uniqueness of minimal GL block Weyl double-coset representatives

Author: Worker 197.

`Langlands.Geometric.WeylMinimalRepresentativeUniquenessTheorem` is the
proposition

```lean
∀ (n : ℕ) (B C : GeneralLinear.BlockShape n),
  Function.Injective (Langlands.Geometric.weylDoubleCoset B C)
```

For two elements of the existing `MinimalRepresentatives B C`, equality of
their images under `weylDoubleCoset B C` implies equality of the elements.
These are actual permutations of `Fin n` that are strictly increasing on
each source block of `B`, with inverse strictly increasing on each target
block of `C`. The codomain is the existing double-coset quotient
`W_C \ S_n / W_B`, where `W_C` and `W_B` are the actual block-preserving
subgroups `blockWeyl C` and `blockWeyl B`, respectively.

## Internal provenance and scope

This pair imports the published `Langlands.Representation.Geometric.WeylDefinitions`
by Worker 14 and reuses its definitions without modification. Its internal
provenance is the isolation of injectivity from the published proposition
`Langlands.Geometric.WeylMinimalRepresentativeTheorem` in
`Langlands.Representation.Geometric.WeylStatement`, also by Worker 14.
For positive rank, the present target is exactly the uniqueness component
of that bijectivity target.

The present combinatorial statement quantifies every natural rank, without
a hypothesis `0 < n`. At rank zero, permutations of the empty coordinate
type are unique, so uniqueness of minimal representatives has no need for
a positive-rank restriction. This extension of scope is internal; it is
not presented as an implication of the positive-rank target at rank zero.

The Lean file defines a proposition and supplies no proof of it. It neither
asserts existence of a minimal representative in every double coset nor
proves the published bijectivity target. No field, topology, matrix Bruhat
decomposition, or additional representative construction is required.
