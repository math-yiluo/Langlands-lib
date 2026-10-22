# Change of the additive character on Whittaker functionals

Worker 31 implements the change-of-additive-character interface for the
Whittaker functionals and coefficient models of `GL_(n+1)(F)`. The source is
the remark in Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg
Convolutions* (1983), §2.1, printed page 385, read directly from the original
scan. The source is registered as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The remark says that if `λ` satisfies the Whittaker condition for `θ`, then
`μ(v) = λ(π(a)v)` with `a` diagonal satisfies it for `θ'(n) = θ(a n a⁻¹)`. In
particular `ψ` may be replaced by `ψ̄`. This module makes the remark explicit
for every scaled character `x ↦ ψ(a*x)`, with the specific diagonal matrix
that realizes it.

## The diagonal element

`characterChangeElement a n` is `d_a = diag(a^n, a^(n-1), ..., a, 1)` in
`GL_(n+1)(F)`, for `a : Fˣ`. Entry `i` (counting from zero) is `a^(n-i)`. It is
built directly as a unit of the matrix ring from Mathlib's `Matrix.diagonal`,
with inverse `diag(a^(-n), ..., 1)`. The Library has no diagonal-torus
embedding to reuse. `characterChangeElement_inv` proves `d_a⁻¹ = d_(a⁻¹)`, and
`characterChangeElement_one` proves `d_1 = 1`. The last diagonal entry is `1`.

`characterChangeElement_conj_apply` computes the entries of `d_a g d_a⁻¹` as
`a^(n-i) g_ij a^(-(n-j))`. Hence conjugation preserves the published
`upperUnipotent` subgroup of Worker 6's `Group/GL/UpperUnipotent`: strictly
lower entries stay zero and diagonal entries stay one. `characterChangeConj`
is this conjugation as a homomorphism of the subgroup, the restriction of
Mathlib's `MulAut.conj`. `characterChangeConj_adjacent` proves that it
multiplies every first-superdiagonal entry by `a`, since
`a^(n-i) a^(-(n-i-1)) = a`.

## Characters

The published `standardCharacter ψ n` of `Whittaker/GeneralLinear` is `ψ` of
the first-superdiagonal sum. The scaled additive character is the published
`ψ.scale a` of Worker 20's `HarmonicAnalysis/CharacterTransport`, with
`ψ.scale a x = ψ(a*x)`. `standardCharacter_characterChangeConj` proves
`standardCharacter ψ n (d_a u d_a⁻¹) = standardCharacter (ψ.scale a) n u`.
This is the source's `θ'` for this `a`. The inverse-character version follows by
inverting. The two `_inv` lemmas give the reverse direction: the character of
`ψ.scale a` on `d_(a⁻¹) u d_(a⁻¹)⁻¹` is that of `ψ`, using the published
`scale_scale` and `scale_one`. These parts need `IsTopologicalRing F`, as
`ψ.scale` does.

## Functionals and models

For a complex representation `π` of `GL_(n+1)(F)` and a standard functional
`ℓ` for `ψ`, `characterChangeFunctional` is `v ↦ ℓ(π(d_a) v)`. It is a
standard functional for `ψ.scale a`. The proof writes `d_a u` as
`(d_a u d_a⁻¹) d_a` and applies the functional's equivariance.
`characterChangeInverseFunctional` does the same for inverse-character
functionals. `characterChangeFunctionalEquiv` and
`characterChangeInverseFunctionalEquiv` are linear equivalences, with inverse
`ℓ' ↦ ℓ' ∘ π(d_(a⁻¹))`. In particular the two functional spaces have the same
dimension, so `π` is generic for `ψ` exactly when it is generic for
`ψ.scale a`, although that corollary is not stated separately.

`characterChangeFunctional_coefficient` proves that the coefficient
`g ↦ ℓ(π(d_a) π(g) v)` of the translated functional is the coefficient of `ℓ`
evaluated at `d_a g`. `characterChangeFunction` and
`characterChangeInverseFunction` are left translation by `d_a`, as linear maps
from the published `equivariantFunctions` space for one character to the space
for the other. `characterChangeFunction_coefficientModel` and its inverse
analogue prove that the coefficient model of the translated functional is
exactly the image of the coefficient model of `ℓ` under left translation.

The module states nothing about zeta integrals. Their behaviour under this
change, and the independence of L-factors from `ψ`, are separate obligations.
They need the left-translation behaviour of the quotient measure under `d_a`.
