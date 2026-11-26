# The diagonal of the kernel is the twisted constant term

Module `Langlands.BaseChange.TwistedVanDijk.Diagonal`. With the notation of
`Langlands.BaseChange.TwistedVanDijk.Operator`, it identifies the sum of the diagonal kernel
values over the cosets of a level with the twisted constant term of Henniart–Lemaire,
*Changement de base et induction automorphe pour GL_n en caractéristique non nulle* (2011),
II.4.5 (printed p. 86), `φ^{P,σ}(x) = δ_P(x)^{1/2} ∫_U ∫_K φ(k⁻¹ x u σ(k)) dk du`, evaluated at
`σ(m)`.

## Statement

`sum_kernelValue_diag`: for a level `L` of a test function `φ`, with `c = μK(K')` and `μK` the
Haar probability measure of `K`, and every `m ∈ M`,

`∑_{x ∈ K/K'} c · k(rep x, rep x)(m) = δ_P(σ(m))^{1/2} ∫_U ∫_K φ(κ⁻¹ σ(m) y σ(κ)) dκ dy`,

where `k(g, y)(m) = δ_P(m)^{1/2} ∫_U φ(g⁻¹ σ(m u y)) du` is `kernelValue`.

## Proof

1. The function `κ ↦ k(κ, κ)(m)` on `K` is right invariant under `K'`: the kernel is right
   invariant under `K'` in each argument (`kernelValue_mul_right_left`,
   `kernelValue_mul_right_right`, using `σ(K') ⊆ K'`). So the finite sum is the integral
   `∫_K k(κ, κ)(m) dκ = δ_P(m)^{1/2} ∫_K ∫_U φ(κ⁻¹ σ(m u κ)) du dκ`
   (`integral_eq_sum_quotient_out`).
2. The integrand is continuous on `K × U` and vanishes unless `u` lies in the compact set
   `{m⁻¹ σ⁻¹(κ s) κ⁻¹ : κ ∈ K, s ∈ supp φ}` (intersected with the closed subgroup `U`); it is
   therefore integrable, and Fubini (`integral_integral_swap`) exchanges the integrals over `K`
   and `U`. Since `σ(m u κ) = σ(m) σ(u) σ(κ)`, the result is
   `δ_P(m)^{1/2} ∫_U ∫_K φ(κ⁻¹ σ(m) σ(u) σ(κ)) dκ du`.
3. The substitution `u ↦ σ(u)` preserves Haar measure on `U` (`map_unipotentAut_eq`).
4. `δ_P(σ(m)) = δ_P(m)` (`leviModulus_leviAut`).
