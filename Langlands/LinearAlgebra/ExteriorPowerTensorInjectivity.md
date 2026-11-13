# Injectivity of exterior antisymmetrization

For a free module `M` over a commutative ring `R`,
`Langlands.LinearAlgebra.exteriorPowerToTensorPower_injective` proves injectivity of
Mathlib's `exteriorPower.toTensorPower R M n`, for every natural degree `n`.
The map sends an exterior monomial to the signed sum of the tensor monomials
indexed by all permutations. No finiteness, characteristic or factorial
invertibility hypothesis occurs.

This is an internal algebraic lemma for the field-cohomology primitive-class
argument. It does not construct an exterior-power comparison with cohomology.
The implementation uses Mathlib's exterior dual pairing: if the
antisymmetrization of `x` vanishes, every exterior product of linear forms pairs
to zero with `x`. For a chosen basis, the coordinate forms of the induced
exterior-power basis are such pairings. Every coordinate of `x` therefore
vanishes, so `x = 0`. Applying this kernel computation to `x - y` gives
injectivity. The temporary choice of a basis is confined to the proof.
