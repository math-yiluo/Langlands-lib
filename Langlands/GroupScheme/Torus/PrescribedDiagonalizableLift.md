# Reparametrizing a clopen lift to match a prescribed fibre

This internal construction uses published Hom comparison for
diagonalizable groups over local rings.

Over any local ring `A`, suppose a clopen homomorphism `j₁ : C₁ → H`
from a relatively diagonalizable group is an isomorphism on the special
fibre. For another relatively diagonalizable group `C₀` and any prescribed
special-fibre isomorphism `e₀ : (C₀)_k ≅ H_k`,
`reparametrize_clopen_lift` constructs a clopen homomorphism `C₀ → H`
whose special-fibre map is exactly `e₀.hom`.

The special-fibre map from `C₀` to `C₁` obtained by composing `e₀` with
the inverse of the special fibre of `j₁` lifts uniquely between the two
diagonalizable groups. Published local Hom comparison reflects its
isomorphism property. Precomposing `j₁` with this lifted isomorphism
preserves both immersion properties and gives the exact prescribed map.
There is no Henselianity, Noetherianity, flatness or smoothness hypothesis
on the base or ambient group beyond the stated existence of `j₁`.
