# The quotient formula for the real Godement column integral

This statement formalizes the passage from equation (7.7) to equation (7.8)
in Jacquet's *Archimedean Rankin-Selberg Integrals* (2009), §7.2,
pp. 48–50. The test is a rectangular Schwartz function and the lower
coefficient belongs to the uniform real Whittaker model for parameter `−a`.
The lower rank is `m = d + 1` and the upper rank is `m + 1`.

Use the variables of `RealGodementStepFubini` to compare with the source.
For Jacquet's translators `h_J`, `g_J`, set `h = h_J w_m` and
`g = w_(m+1) g_J`. The variables `x = w_m X` and `u = v` turn
`Φ(h_J [v,X] g_J)` into `Φ(h [x,w_m u w_m] g)`. The choice `a = −b`
for Jacquet's parameter `b` converts both conjugated phases and preserves
their self-dual measures. The coefficient argument satisfies
`w_m h⁻¹ = h_J⁻¹`. The two determinant weights acquire the same product
of signs from `w_m` and `w_(m+1)` on both sides of the formula. Their absolute
determinants are one.

The column change of variables gives the frequency `h⁻ᵀ e₀` and the factor
`|det h|⁻¹`. Applying the polar decomposition of the real inducing character
leaves parity `c.parity` and complex determinant exponent `c.exponent + d/2`
in the Mellin integral. The coefficient is evaluated at `w_(d+1) h⁻¹`.
Absolute convergence follows from the real first-column convergence theorem.

The substitution `h = k⁻¹ w_m` preserves real general-linear Haar. The
compatible Weil formula then expresses the integral as an upper-unipotent
orbit average over the left quotient. Inverting the unipotent variable
preserves its Haar because that measure is both left and right invariant.
The coefficient contributes the positive standard character in the inverted
coordinate. The Weyl conjugate lower-unipotent matrix has determinant one
and fixes the first-column frequency under inverse transpose, so changing
columns replaces the trailing identity by this lower-unipotent matrix.
The real Godement step Fubini formula now identifies the orbit integral
with the descended quotient kernel.

The supplied subgroup Haar is a positive multiple `λ` of the self-dual
entry-product Haar. The equality retains this multiplier, which depends
only on the quotient measure data and the additive character. Absolute
integrability of the Weil average and positivity of `λ` give absolute
integrability of the outer quotient kernel.
