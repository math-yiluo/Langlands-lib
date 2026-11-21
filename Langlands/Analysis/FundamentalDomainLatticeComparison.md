# Comparing fundamental domains of two lattices with a common Levi part

Module `Langlands.Analysis.FundamentalDomainLatticeComparison`, namespace
`Langlands.Analysis.LatticeComparison`. Main result: `mul_setLIntegral_eq`. Its statement form is
`LatticeComparisonStatement`, proved by `latticeComparison`.

## Statement

The ingredients are as follows.

- `H` and `V` are measurable groups (measurable multiplication and inversion), in arbitrary
  universes.
- `μ` is a left-invariant s-finite measure on `H`.
- `ν` is a left- and inversion-invariant s-finite measure on `V`.
- `j : V →* H` is a measurable injective homomorphism.
- `Λ`, `Λ'` are countable subgroups of `H`, with measurable strict fundamental domains `D`, `D'`:
  every `x` has exactly one `l` with `l x ∈ D` (resp. `D'`).
- `Γ`, `Γ'` are countable subgroups of `V`, with `j(Γ) ⊆ Λ`.
- `C` is a measurable fundamental domain of `Γ` in `V`, and `C'` a fundamental domain of `Γ'`
  (Mathlib's `IsFundamentalDomain`, for left multiplication and `ν`).
- `Λ` normalizes `j(V)` through maps `cj l : V → V` with `j(cj l v) = l j(v) l⁻¹`. These maps
  preserve `ν` and map `Γ` into `Γ`.
- A type `M` with `m : M → H` and bijections `e : M × Γ ≃ Λ`, `e' : M × Γ' ≃ Λ'` satisfying
  `e(x, γ) = m(x) j(γ)` and `e'(x, γ') = m(x) j(γ')`. So both lattices are products with the same
  factor `M`.

Then for every measurable `φ : H → [0, ∞]` that is left-invariant under `Λ` and under `j(V)`:

`ν(C) · ∫_{D'} φ dμ = ν(C') · ∫_D φ dμ`.

No finiteness of `ν(C)` or `ν(C')` is assumed. The identity is in `[0, ∞]`.

## Proof

1. `setLIntegral_eq_setLIntegral_mul_count`: unfolding `1 = Σ_{l ∈ Λ} 1_D(l·)` and using left
   invariance of `μ` and `Λ`-invariance of `φ` gives `∫_{D'} φ = ∫_D φ · N`, where
   `N(g) = Σ_{l ∈ Λ} 1_{D'}(l g)`. The function `N` is `Λ`-invariant: reindex by right
   multiplication.
2. The fibre-average identity `FibreAverage.setLIntegral_fibreAverage` (module
   `Langlands.Analysis.FundamentalDomainFibreAverage`) is applied to `F = φ · N`. With
   `φ(j(v) g) = φ(g)` it gives `ν(C) ∫_D φ N = ∫_D φ(g) ∫_C N(j(v) g) dν dμ`.
3. `tsum_setLIntegral_eq_tsum_lintegral`: summing over `Λ ≅ M × Γ` and integrating over `C` equals
   summing over `M` and integrating over `V`. This uses Mathlib's
   `IsFundamentalDomain.lintegral_eq_tsum''`. The same holds for `Λ'`, `Γ'`, `C'`. Hence
   `∫_C N(j(v) g) dν = Σ_{l' ∈ Λ'} ∫_{C'} 1_{D'}(l' j(v) g) dν = ∫_{C'} 1 dν = ν(C')`, since
   `D'` is a strict fundamental domain of `Λ'`.
4. Combining these gives `ν(C) ∫_{D'} φ = ν(C') ∫_D φ`.

## Use and provenance

This is an abstract measure-theoretic lemma, derived for the proof of Bernstein–Lapid,
*On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), 187–234,
registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §§7.3–7.5
(pp. 214–217). The intended instance:

- `H = G(𝔸)`, `V = U_P(𝔸)`.
- `Λ = P₀(F) = (M_P ∩ P₀)(F) · U_P(F)` and `Λ' = a Λ a⁻¹`, for `a` in the split component of `P`.
  This `a` centralizes `M_P`.
- `Γ = U_P(F)`, `Γ' = a Γ a⁻¹`, `C' = a C a⁻¹` and `D' = a D`.

With these choices the lemma expresses how left translation by `a` acts on integrals of functions
invariant under `P₀(F) U_P(𝔸)`. The ratio `ν(aCa⁻¹)/ν(C)` is the modulus of `a` on `U_P(𝔸)`. The
source uses this implicitly when it views the translations `σ_α` as bounded operators on weighted
spaces of functions on `P₀(F)U_P(𝔸)\G(𝔸)`. The adelic instantiation and the identification of the
ratio with the modular character are not part of this module.
