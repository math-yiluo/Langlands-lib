# Proof of polynomial bounds on compact actual lattice charts

The implemented argument first proves monotonicity of the actual
residue-normalized absolute value with respect to the valuative relation.
This follows by composing the order-preserving value-group normalization
with the increasing map from integral multiplicative valuations to positive
real magnitudes.

For a compact rational-point set and its inverse, the published actual matrix
entry bound supplies a common valuative upper bound for every matrix entry.
Monotonicity converts it to a common residue-normalized real bound for both
the matrix and its inverse. Taking the maximum with one gives a bound at least
one for `rationalMatrixNorm`. This argument uses the canonical rational-point
topology throughout and does not identify it with the topology induced by the
auxiliary normed-field instance.

The published `compactTranslateLatticeBound`, with zero coordinate weights,
extends the assumed product-exponential estimate uniformly to the two compact
outer translates and the finite middle translate. Since the coordinate type
is finite and `q > 1`, choose an integer exponent for each coordinate radius
and sum these exponents to obtain a single natural number `d` with

`∏ i, a i ^ m i ≤ (q ^ (∑ i, m i)) ^ d`.

The compact matrix-norm bounds give positive constants `B₁`, `B₂`, and `B₃`
for the two outer sets and the finite middle set. If
`g = k₁ * τ m * t * k₂`, write
`τ m = k₁⁻¹ * g * k₂⁻¹ * t⁻¹`. Inversion invariance and submultiplicativity
of the actual matrix norm show

`rationalMatrixNorm F ρ (τ m) ≤ B₁ * B₂ * B₃ * rationalMatrixNorm F ρ g`.

The helper `rationalCompactLatticePolynomialBound_of_power_height` accepts the
more general geometric premise

`q^(sum_i m_i) ≤ A * rationalMatrixNorm F ρ (τ m)^D`

for a natural number `D`. Put `B = B₁ * B₂ * B₃`. The compact comparison gives
`q^(sum_i m_i) ≤ (A * B^D) * rationalMatrixNorm F ρ g^D`.
Raising to `d` proves a coefficient bound with natural exponent `D * d` and
strictly positive constant `C * (A * B^D)^d`. This includes `D = 0` without a
separate argument. The exact theorem `rationalCompactLatticePolynomialBound`
applies this helper with `D = 1`; it proves the unchanged first-power-height
statement with constant `C * (A * B)^d`.

The construction also covers an empty coordinate type: the relevant product
is one and the sum of coordinate exponents is zero. No proof of the geometric
coordinate comparison, a global Cartan cover, or central-factor control is
claimed here. The statement and proof are internal analytic consequences of
the imported published constructions, rather than a direct transcription of
a literature theorem.
