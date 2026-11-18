# Averaging polynomial functions using an invariant coordinate integral

The internal construction `MatrixRepresentation.PolynomialAverage.reynolds`
takes an affine group scheme `G` over any field `k`, an actual finite matrix
representation `ρ`, and a supplied `CoordinateIntegration.InvariantIntegral G`.
It returns a `k`-linear endomorphism of `MvPolynomial n k`. No characteristic,
finite-type, reducedness, smoothness or connectedness premise is used. The
finite index type `n` has decidable equality.

The construction satisfies three laws, with invariance understood on every
scheme test exactly as in `MatrixRepresentation.IsInvariantPolynomial`:

- `reynolds_invariant`: its value at every polynomial is invariant.
- `reynolds_eq_self`: it fixes every invariant polynomial.
- `reynolds_mul`: for an invariant polynomial `s` and any polynomial `F`,
  averaging `s * F` gives `s` times the average of `F`.

These laws give the Reynolds projection needed by the finite-generation
argument. This module does not assert finite generation or construct the
supplied integral. Its provenance is an internal derivation from the published
coordinate-integral and universal-polynomial interfaces.

For a vector `x` over any commutative `k`-algebra `A`, `orbit ρ x` evaluates a
polynomial at the inverse universal translate of `x` in
`A ⊗[k] CoordinateIntegration.Coord G`. Thus it represents the function
`h ↦ F(ρ(h⁻¹)x)`. The inverse makes pullback by left translation in the
integration variable equal inverse translation of `x`. The proof of
`orbit_leftTranslation` uses naturality of the actual affine action and
`(t h)⁻¹ = h⁻¹ t⁻¹`.

The linear endomorphism `reynolds` contracts the coordinate factor in the orbit
of the generic vector of polynomial variables. The lemma `orbit_naturality`
commutes this orbit map with a map of coefficient algebras. Naturality of
contraction then gives `eval_reynolds`: evaluating the averaged polynomial at
`x` equals averaging the orbit of `x`. Translation invariance of the integral
and `orbit_leftTranslation` give `eval_reynolds_action` over every affine test
algebra.

The helper `invariant_of_affine_eval` promotes such affine evaluation identities
to all-scheme invariance. It evaluates at the generic vector over a polynomial
extension of the chosen coordinate algebra, obtaining a coefficientwise
polynomial identity. The canonical affine-sections isomorphism transports this
identity to global sections. The chosen coordinate presentation is an
isomorphism and hence an epimorphism, so the published
`isInvariantPolynomial_of_epi_polynomial` proves the universal identity and
invariance on every scheme test. This argument does not use density of field
points or assume that `k` is infinite.

For invariant `F`, its affine invariance identifies `orbit ρ x F` with the
constant tensor of its value at `x` (`orbit_invariant`). Normalization of the
integral therefore gives `reynolds_eq_self`. Finally `orbit` is an algebra
homomorphism, so an invariant factor becomes a tensor from the coefficient
algebra. Linearity of contraction over that algebra moves the factor outside
the integral and proves `reynolds_mul`.
