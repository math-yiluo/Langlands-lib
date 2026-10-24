# Compact average of the root-coordinate expansion

`Langlands.RankinSelberg.EqualRankCompactRootExpansionStatement F T n` is an
internal conditional proposition for the supplied p-adic field and topology,
in rank `n + 1`, including rank one. The two representation spaces have
independent universes. Both representations are assumed smooth and are assumed
to satisfy the standard- and inverse-character `CoefficientTorusExpansion`
propositions, respectively.

Let `K` be the integral general linear subgroup from `T`, and let `κ` be the
restriction of the actual `generalLinearHaar` to `K`. In unit coordinates put

```text
d(a)_i = ∏_{j ≥ i} a_j,
w(a) = (∏ i, (T.normalizedAbs(a_i) : ℂ)^((i + 1)(n - i)))⁻¹,
v(a,s) = ∏ i, (T.normalizedAbs(a_i) : ℂ)^((i + 1)s).
```

The first powers in `w` are natural powers; those in `v` are complex powers.
Indices range from zero through `n`. There is a finite indexed family `η_j` of
continuous complex functions on the full unit torus, each with finite-dimensional
left-translation span. This family is chosen before the two functionals, the
two actual coefficient-model vectors and the Schwartz row test.

For every such choice of data, there are finitely many real coefficients `c_t`
and full-coordinate Schwartz functions `Ψ_{t,j}`. The coefficients are
nonnegative and sum to one. They and the Schwartz functions are chosen before
every unit tuple `a` and spectral parameter `s`. With

```text
H(z) = equalRankFunction ψ (normalizedAbsoluteValue T) f.val f'.val Φ s
         (diagonalUnits(d(a)) * z) * w(a),
S_t  = ∑ j, Ψ_{t,j}(a) * η_j(a) * v(a,s),
```

the proposition asserts that `H` is integrable for `κ` and that

```text
∫ H(z) dκ(z)       = ∑ t, (c_t : ℂ) * S_t,
∫⁻ ‖H(z)‖ₑ dκ(z)  = ∑ t, ENNReal.ofReal(c_t) * ‖S_t‖ₑ.
```

The second identity retains the norm of each inner sum; it does not replace
it with a sum of norms. No nonzero condition is imposed on either functional.
The finite family may repeat function values.

This is an internal combination of the published root-model expansion and
normalized compact-integration interfaces with the root spectral-weight
identity. Compact integration chooses representatives and weights uniformly
in the group argument and `s`. At those representatives, root-model expansion
supplies the Schwartz families and the determinant norm is one. Multiplication
by the inverse-modulus factor and the explicit spectral product gives the
displayed finite formulas. This provenance does not attribute an independent
theorem to the literature. The assertion concerns the compact variable only;
torus convergence, quotient integration, rational continuation and denominator
control remain separate obligations.
