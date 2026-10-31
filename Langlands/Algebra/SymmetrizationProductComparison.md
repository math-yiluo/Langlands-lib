# Filtered product comparison

Let `R : Type` be a field and `L : Type v` an arbitrary-universe Lie algebra
over `R`. Write `s` for the actual whole linear symmetrization into the genuine
enveloping algebra.
`symmetricAlgebraSymmetrizeMultiplicationError R L` is the bilinear map
`(P, Q) ↦ s(P * Q) - s(P) * s(Q)`. Bilinearity follows from the linearity of `s`
and the scalar-compatible multiplications in the two actual algebras; this
construction does not require characteristic zero.

With `CharZero R`,
`symmetricAlgebraSymmetrize_prod_mul_sub_mem` proves that this error for the
monomials associated to lists `l` and `m` belongs to genuine enveloping
filtration degree at most `l.length + m.length - 1`.
If either list is empty, its monomial and symmetrization are one, so the error
vanishes. Otherwise, let `w(l)` and `w(m)` be the corresponding ordered
enveloping words. Apply the existing strict word comparison to the concatenated
list and to both factors. The concatenated symmetric monomial is the product
of the two monomials, and its ordered word is `w(l) * w(m)`.
The remaining difference is controlled by the identity

```text
s(P) * s(Q) - w(l) * w(m)
  = (s(P) - w(l)) * s(Q) + w(l) * (s(Q) - w(m)).
```

The two factor comparisons lower the total degree by one, and the genuine
filtration multiplication bound places both summands in the asserted piece.
Subtracting their sum from the concatenated comparison proves the result.

`symmetricAlgebraSymmetrize_mul_sub_mem` extends this to
`P ∈ symmetricDegreeFiltration R L p` and
`Q ∈ symmetricDegreeFiltration R L q`, with error in
`degreeFiltration R L (p + q - 1)`. Two linear-span inductions use the
monomial result and monotonicity of the filtration; addition and scalar
multiplication preserve membership because the error is bilinear.
Natural-number subtraction is retained, including at degree zero.

This is internal derived infrastructure. Its ingredients are the actual bounded
monomial spans, the genuine filtration and its multiplication rule, and the
existing characteristic-zero strict monomial comparison for the whole
symmetrization map. No finite-dimensionality is needed. The result is a filtered
comparison; it does not assert that symmetrization is an algebra homomorphism,
prove a PBW isomorphism, lift invariants, establish central generation or prove
the automorphic differential-growth theorem.
