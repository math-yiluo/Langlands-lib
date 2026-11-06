# Tangent conjugation for the actual positive right-orbit derivative

For a smooth real Lie group, `groupTangentConjugation` is the actual
manifold derivative at the identity of the inner automorphism
`h ↦ g * h * g⁻¹`. It is a real continuous linear map on the identity
tangent space.

For a real C∞ function `f : G → ℂ` (Lean:
`ContMDiff I 𝓘(ℝ, ℂ) ∞ f`), arbitrary `g, x : G`, and any identity-tangent
vector `X`, the covariance identity compares `D(X)f(x*g)` with the
derivative of `y ↦ f(y*g)` at `x` in direction
`groupTangentConjugation g X`. The proof applies the manifold chain rule
to the conjugation map and the orbit function `h ↦ f((x*h)*g)`;
smoothness of `f` supplies the latter map's differentiability. Their composite equals
`h ↦ f((x*g)*h)` by the group laws. This proves the identity for the
original positive right-orbit differential, with no supplied covariance
assumption.

This is an internal differential construction. It neither computes an
algebraic adjoint determinant nor identifies it with a Haar modulus.
