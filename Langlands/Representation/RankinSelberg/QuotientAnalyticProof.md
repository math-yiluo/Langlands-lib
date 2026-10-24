# Proof of conditional analytics for equal-rank quotient integrals

`Langlands.RankinSelberg.equalRankQuotientAnalytic` proves exactly
`EqualRankQuotientAnalyticStatement F T n`, with independent field and
representation universes. It composes `equalRankRootAverageAnalytic`,
`equalRankIntegrandContinuous` and `quotientRootIntegration`. The full
Mellin, ordinary-diagonal Iwasawa and both coefficient-expansion premises
remain explicit. Both representations need only be smooth, and zero
functionals remain allowed.

The proof installs the topology and valuation from the supplied `T`,
together with the Borel structures in the target. It uses the normalized
product multiplicative Haar measure `dA` and the actual general linear
Haar measure restricted to the integral subgroup, `κ`. With suffix-product
diagonal map `d` and inverse-modulus weight `w`, the actual weighted
function is

```text
H(f,f',Φ,s,a,z) = equalRankFunction ψ (normalizedAbsoluteValue T) f.val f'.val Φ s
                   (diagonalUnits(d(a)) * z) * w(a),
J(f,f',Φ,s) = ∫ a, ∫ z, H(f,f',Φ,s,a,z) dκ(z) dA(a).
```

The root-average theorem supplies a nonzero Laurent denominator `D`
before either functional and before any compatible measure is introduced.
For fixed functionals, it also supplies convergence, rationality and
denominator control for `J`.

The normalized absolute value is continuous by
`T.continuous_normalizedAbsHom` and the real coercion from nonnegative
reals. Applying the integrand continuity theorem therefore makes every
actual quotient integrand measurable for the Borel structure.
`quotientRootIntegration`, applied to this measurable function and the
given compatible measure, identifies its integrability with finiteness of
the compact-first iterated norm integral. Its weighted pullback agrees
definitionally with `H`, through the actual quotient projection.

For each pair of coefficient vectors and each Schwartz row test, the
root-average estimate supplies a right half-plane where this norm
integral is finite. The proof first deduces `EqualRankConverges` there.
Only then does it apply the integral-equality clause of the quotient/root
theorem to identify `equalRankModelIntegral` with `J` on that half-plane.

`continuation_of_eq_on_right` transfers a rational continuation of `J` to
the quotient integral, preserving reduced-denominator nonvanishing. For
an arbitrary member of `equalRankRationalValues`, the proof extracts its
actual coefficient vectors, test and continuation. Applying the same
transfer lemma to the reverse equality makes it a continuation of `J`;
the root-average denominator assertion then clears it using the original
`D`. Thus this one denominator works for every rational value and every
compatible measure. No equality outside a convergence half-plane is
asserted or needed.

This is an internal composition of the named interfaces. It does not
prove the assumed Mellin, Iwasawa or coefficient-expansion inputs, the
Whittaker-type expansion theorem, a unit-value test or normalized-generator
existence. In particular it is a conditional prerequisite of the host
`EqualRankAnalyticStatement`, whose full unconditional proof remains a
separate obligation.
