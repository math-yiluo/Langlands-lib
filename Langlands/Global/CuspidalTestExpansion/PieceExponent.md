# Exponents of intertwined generalized eigenfunctions

Module `Langlands.Global.CuspidalTestExpansion.PieceExponent`
(namespace `Langlands.Global.StandardParabolicFamily`).

## Statements

- `HasPolynomialOrbit.mono`: the polynomial orbit condition `HasPolynomialOrbit J λ k h` (for
  every `g`, `x ↦ h(x g) x^{-λ}` on `𝔄_{P_J}` is a polynomial of degree `≤ k` in the logarithm `log(x)` (`characterLog`)) implies
  the same condition for every `m ≥ k`.
- `exists_offset_hasPolynomialOrbit_intertwiningIntegral`: let `n` be a rational point and
`c : M_J → M_{I₁}` with `IsWeylConjugation (fam.p I₁) (fam.l I₁) (fam.p J) (fam.l J) n c`
(so `n M_{I₁} n⁻¹ = M_J`), `π : P_J → M_J` a projection with `fam.l J ≫ π = 𝟙`, and `K` an
Iwasawa subgroup for `P_{I₁}`. There is one parameter `offset` of `P_J` such that, for every
continuous `h` on `G(𝔸)` that is left invariant under `U_{I₁}(𝔸)` and has unnormalized exponent
`ν` along `I₁` with polynomial degree at most `k` (`HasPolynomialOrbit I₁ ν k h`), and every `λ`
for which the intertwining integrands of all positive split translates of `h` are integrable, the
intertwining integral

`y ↦ ∫_{(U_J(F) ∩ n U_{I₁}(𝔸) n⁻¹) \ U_J(𝔸)} h_λ(n⁻¹ v y) dv`

(`hK.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) n h λ`) has unnormalized exponent
`weylParameter (fam.l I₁) c π (ν + λ) + offset` along `J`, with the same degree bound `k`
(`HasPolynomialOrbit J _ k`). The offset does not depend on `h`, `ν`, `k` or `λ`. The statement
only asserts that such an offset exists. The proof takes the parameter of `P_J` whose character
power is the scaling factor of the quotient measure on `H \ U_J(𝔸)`, where
`H = (U_J ∩ n U_{I₁} n⁻¹)(𝔸)` is the closed adelic stabilizer: for `t ∈ 𝔄_{P_J}` with point
`x_Q ∈ P_J(𝔸)`, `x_Q^{offset}` is the Haar factor of the conjugation `v ↦ x_Q v x_Q⁻¹` on
`U_J(𝔸)` divided by the Haar factor of its restriction to `H` (`intertwiningHaarOffset`). This
factor accounts for the modulus character of `M_J` on the quotient
`(n U_{I₁} n⁻¹ ∩ U_J)(𝔸) \ U_J(𝔸)`, which Bernstein–Lapid, *Meromorphic continuation of
Eisenstein series* (2024), use through (6.5), p. 201, to prove (6.4); there the normalization by
`ρ` absorbs it. The theorem is the exponent bookkeeping behind their §6.10 for the terms of the
constant term formula (6.17).

## Proof

`HasPolynomialOrbit.mono` holds because the spanning set of `polynomialFunctions _ k` (products
of at most `k` linear forms) is contained in that of `polynomialFunctions _ m`.

The offset is the one supplied by `intertwiningHaarOffset` for the conjugation action of
`𝔄_{P_J}` on `U_J(𝔸)` and on `H`. Fix `g`. Since `h` has exponent `ν` and degree `≤ k`, for each point `z` of
the integration domain there is a polynomial `Q_z` of degree `≤ k` with
`h(b z) b^{-ν} = Q_z(log(b))` on `𝔄_{P_{I₁}}`. Put `f(q, T) = (height power of z_q) · Q_{z_q}(T)`;
for each `T` this is a positive translate's integrand up to a constant factor, hence integrable,
so `exponentPolynomialIntegral` shows `T ↦ ∫ f(q, T) dq` is a polynomial of degree `≤ k`.
Composing with the linear map `L` dual to `π ≫ c ≫ fam.l I₁`
(`polynomialFunctions_comp_linear`) gives the polynomial for `J`, again of degree `≤ k`.

For `t ∈ 𝔄_{P_J}`, let `x_Q` be its point of `P_J(𝔸)` and `x_P` its transport to `P_{I₁}(𝔸)`
(`weylPositiveTransport`: `x_P = n⁻¹ x_Q n`, logarithms related by `L`, powers related by
`weylParameter`). Conjugation `α : v ↦ x_Q v x_Q⁻¹` of `U_J(𝔸)` preserves `H`
(`positiveIntertwiningRadicalAction_mem_stabilizer`), and the change of variables of
`intertwiningIntegralConjugation` gives

`Int h (x_Q g) = (Δ(α) / Δ(α|_H)) · ∫ h_λ(n⁻¹ x_Q v g) dv = (Δ(α) / Δ(α|_H)) · ∫ h_λ(x_P n⁻¹ v g) dv`,

where `Δ` denotes the Haar factor (`mulEquivHaarChar`). By `intertwiningHaarOffset` the factor
`Δ(α) / Δ(α|_H)` is `x_Q^{offset}`. In the remaining integral,
`h_λ(x_P z) = x_P^{ν + λ} · f(q, L(log(x_Q)))` for `z = n⁻¹ v_q g` (`heightPower_map_mul`, the
polynomial `Q_z` and `parameterPower_add`), and `x_P^{ν + λ} = x_Q^{weylParameter (ν + λ)}`.
Hence `Int h (x_Q g) · x_Q^{-(weylParameter (ν + λ) + offset)} = ∫ f(q, L(log(x_Q))) dq`, the
polynomial of degree `≤ k` found above.
