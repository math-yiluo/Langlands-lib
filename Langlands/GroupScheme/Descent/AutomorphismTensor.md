# Tensor decomposition from separated algebra automorphisms

This internal algebra construction concerns commutative rings `R` and `S`, an
`R`-algebra structure on `S`, and a family `s` of actual `R`-algebra
automorphisms of `S`. Its tensor evaluation map sends `a ⊗ b` to the tuple
`a * s i b`.

Suppose the index type is finite and, for distinct indices `i` and `j`, some
`b` has `s i b - s j b` a unit in `S`. The kernels of the two evaluation maps
are then comaximal. Indeed, multiply `1 ⊗ b - s j b ⊗ 1` by the inverse
difference in the first tensor factor. Its two values are `1` and `0`.
That tensor and its complement exhibit comaximality. The Chinese remainder
theorem supplies a tensor with any prescribed tuple of values, proving
surjectivity.

If `S` is nontrivial and finite free over `R`, and the number of indices
equals its `R`-rank, the source and target have equal finite free rank over
`S`. The published Mathlib result for the Orzech property of commutative
rings makes the surjective linear map bijective. The construction `equiv`
packages this canonical map as an actual `S`-algebra equivalence and retains
the pure tensor formula.

These are derived algebra results proved using the imported Chinese remainder
and finite free module theorems. No unramifiedness premise, residue-field
comparison or scheme descent datum is asserted in this module.
