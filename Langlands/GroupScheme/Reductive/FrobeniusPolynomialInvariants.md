# Frobenius descent of actual origin-invariant coordinates

This is a derived supporting construction by Worker 1369. It connects the
actual arbitrary-test origin condition to the polynomial expansion
characterization in `Langlands.Algebra.PolynomialFrobeniusDescent`. It uses
no new assertion from external literature.

For an affine group scheme `G` over a field `k : Type u`, exponential
characteristic `p`, and any natural height `r`, put `q = p ^ r`. Suppose an
algebra equivalence identifies its actual coordinate algebra with
`MvPolynomial σ k`, where `σ : Type` is a small variable type. If an actual
coordinate `b` is right invariant under every intrinsic origin point on
every relative test scheme, then its polynomial image equals `expand q H`
for some polynomial `H`. The expansion replaces each variable by its
`q`-th power and leaves the coefficients unchanged. There is no assertion
that the coefficients themselves have `q`-th roots.

The proof uses the spectrum of each arbitrary commutative coefficient
algebra as an actual test scheme. Two algebra maps whose values have equal
`q`-th powers give congruent actual points. The arbitrary-test congruence
descent theorem gives equal evaluations of `b`. The relative spectrum
adjunction counit is injective and cancels from this equality, yielding
`UniversalPowerInvariant q`. The polynomial characterization then supplies
`H`. The same argument applies after restriction along any actual affine
subgroup homomorphism: the point multiplication and coordinate pullback
identities transfer the given invariance to the subgroup.

The data-valued map
`Dynamic.oppositeUnipotentPolynomialRestriction i ν hT coords χ` restricts
the **entire** left-covariant space for the actual dynamic parabolic
`P(ν)` to the actual opposite unipotent group `U(-ν)`, and then applies the
constructed polynomial coordinate equivalence. Here `G` is smooth,
`hT` supplies a split torus, `coords` is a
`Standard.UnipotentPolynomialCoordinates i (-ν) hT`, and `χ` is an actual
parabolic coordinate. The polynomial coordinate equivalence does not
identify the unipotent group law with addition. Under
`IsConnectedReductive G`, the map is injective by the existing full
opposite-cell restriction theorem and injectivity of the polynomial
coordinate equivalence.

The subgroup adapter shows that an origin-invariant original covariant
coordinate has an expansion under this map. Finally,
`Dynamic.exists_nonzero_expand_of_not_injective` proves that failure of
injectivity of the actual height-`r` quotient restriction supplies an
original covariant vector `f` and a polynomial `F` with all the following
properties:

- `f` is nonzero and its actual height-`r` quotient restriction is zero;
- its full opposite-cell polynomial is `expand q F`;
- `F` is nonzero and its constant coefficient is zero.

The proof first uses the existing stable-kernel and augmentation argument
to obtain an origin-invariant nonzero kernel vector. Polynomial descent
gives `F`. Full restriction injectivity proves `F` is nonzero. The exact
Frobenius-box quotient criterion makes the constant coefficient of the
full restriction zero, and expansion preserves that coefficient. Thus
`F` cannot be a constant polynomial.

The field universe and the relative test schemes remain arbitrary.
Tests need not be affine or reduced; affine spectra are used only as a
permitted subfamily when proving the universal coefficient-algebra
condition. Nonreduced and zero coefficient algebras are allowed. Height
zero, exponential characteristic one, and zero-dimensional opposite
unipotent coordinates need no exceptions. The small-variable restriction
in the generic adapter includes every finite dynamic coordinate set.

This unit does not exclude the resulting nonconstant expanded kernel
vector, prove injectivity at a fixed height, prove the whole-space
Steinberg dimension bound, construct the remaining structural or
highest-weight data, or prove `SteinbergBigCellStatement`.
