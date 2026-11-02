# Finite coefficient families of derivations

For commutative rings `R` and `C`, an `R`-algebra structure on `C`, and a
compatible `C`-module `M`, `derivationFinsuppLinearEquiv` constructs a `C`-linear
equivalence

`Derivation R C (ι →₀ M) ≃ₗ[C] (ι →₀ Derivation R C M)`

when `C` is of finite type over `R`. The index type `ι` is unrestricted, and
`M` is an additive commutative group; no field or flatness hypothesis is used.

This is an internal derived prerequisite for extracting Laurent coefficients
in the weight-decomposition argument. The motivating source is Milne,
*Algebraic Groups* (2017), 12.12, printed pp.234–235 (PDF250–251), which decomposes
representations of diagonalizable groups. This file does not construct a
representation or prove that theorem. Its derivation equivalence is derived
directly from Mathlib's finite-generation and derivation APIs, rather than
asserted to be a statement in Milne.

`derivationCoefficient i` postcomposes a derivation with the `i`-th coordinate
projection. To prove that these coefficient derivations have uniformly finite
support, `derivationCoefficient_finite` chooses a finite set of algebra
generators and takes the union of the supports of their images. Outside that
union, the coefficient derivation vanishes on every generator and hence
vanishes identically, by `Derivation.ext_of_adjoin_eq_top`.
`derivationCoefficients` packages the resulting coefficient family as a linear
map into a finitely supported family.

Conversely, `sumDerivationCoefficients` forms the finite sum of postcompositions
with the coordinate inclusions. Its evaluation formula is proved by linear
induction on finitely supported families, including the individual-coordinate
case. Both inverse laws of `derivationFinsuppLinearEquiv` then follow from
extensionality and the evaluation formulas. The assembly map and its evaluation
formula do not require the finite-type hypothesis; finite type is used only to
construct the uniformly finite coefficient family.
