# Exponents of intertwined generalized eigenfunctions

Module `Langlands.Global.CuspidalTestExpansion.PieceExponent` in namespace
`Langlands.Global.StandardParabolicFamily`.

## Statements

`IntertwiningPolynomialOrbitTransportStatement` concerns the intertwining integral from
`P = P_{I₁}` to `Q = P_J` when a rational point `n` conjugates the Levi of `P` onto that of `Q`.
Write `c : M_J → M_{I₁}` for inverse conjugation, `π : Q → M_J` for the Levi projection, and
`W = weylParameter (fam.l I₁) c π` for the pullback along `π ≫ c ≫ fam.l I₁`. Take an
Iwasawa compact subgroup for `P`. The input function `h` on `G(𝔸)` is continuous and left
`U_{I₁}(𝔸)`-invariant. It satisfies `HasPolynomialOrbit I₁ ν k h`, so the raw shift by a
positive split point `b`, multiplied by `b^{-ν}`, is polynomial of degree at most `k` in
`characterLog b` at each base point. The integrability hypothesis is for the intertwining
integrand of every such left translate of `h`, with twist parameter `λ` and at every base
point.

Under these hypotheses `hasPolynomialOrbit_intertwiningIntegral_halfModulusOffset` proves
that the integral of the twist `h_λ`, over
`(U_J(F) ∩ n U_{I₁}(𝔸) n⁻¹) \ U_J(𝔸)`, has polynomial orbit of degree at most `k` along
`J` with raw exponent

`W(ν + λ) + (ρ_Q − W(ρ_P)) = W(ν − ρ_P + λ) + ρ_Q`,

where `ρ_P` and `ρ_Q` are the Library's `halfModulusParameter`. The offset
`ρ_Q − W(ρ_P)` witnesses `exists_offset_hasPolynomialOrbit_intertwiningIntegral` and is
independent of `h`, `ν`, `λ` and `k`. The lemma `HasPolynomialOrbit.mono` enlarges the
polynomial degree bound by inclusion of the spanning monomials.

## Proof

Fix a base point `g`. At the representative `z_q = n⁻¹ v_q g` of an integration variable `q`,
write `h(b z_q) b^{-ν} = Q_q(characterLog b)`. Put
`f(q,T) = heightPower λ z_q · Q_q(T)`. Each value of `T` is the logarithm of a positive split
point by `standardPositiveLog`. The integrability hypothesis for its translate gives
integrability of `q ↦ f(q,T)`. The theorem `exponentPolynomialIntegral` gives a polynomial
`T ↦ ∫ f(q,T) dq` of degree at most `k`. Its composition with the linear map `L` on logarithms
induced by `π ≫ c ≫ fam.l I₁` has the same degree bound by `polynomialFunctions_comp_linear`.

For a positive split point `x_Q` in `Q(𝔸)`, `weylPositiveTransport` identifies the transported
point `x_P` of `P(𝔸)` with `n⁻¹ x_Q n` under the ambient group maps. It identifies its logarithm
with `L(characterLog x_Q)` and its character powers with the powers at `x_Q` of the pullback
parameters. The theorem `intertwiningIntegralConjugation` moves the left shift by `x_Q` inside
the integral, multiplying it by the quotient Haar factor for conjugation on `U_J(𝔸)` and its
restriction to the closed stabilizer `(U_J ∩ n U_{I₁} n⁻¹)(𝔸)`.

The point `x_Q` comes from the Levi point `m` obtained by mapping the split torus into `M_J`,
and `x_P` comes from `c(m)`. At `m`, `intertwiningStabilizerModulus` evaluates the factor as
`x_Q^{ρ_Q} · x_P^{-ρ_P}`. The power pullback and `parameterPower_add` rewrite this factor as
`x_Q^{ρ_Q − W(ρ_P)}`. Inside the translated integral, `heightPower_map_mul` and the polynomial
orbit of `h` give `h_λ(x_P z_q) = x_P^{ν + λ} · f(q,L(characterLog x_Q))`. Multiplying the
shifted integral by the inverse of the stated raw character value cancels the scalar factors
and yields the polynomial of degree at most `k` constructed above.

## Source

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series* (2024), p. 201,
(6.4) and (6.5), give the intertwining covariance and identify the modulus on the unipotent
quotient as `ρ_Q − wρ_P`. The polynomial-orbit statement uses this identity in the raw
translation convention and carries the source logarithmic polynomial through the integral.
