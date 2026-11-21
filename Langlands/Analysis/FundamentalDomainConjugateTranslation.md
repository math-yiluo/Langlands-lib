# Left translation by an element centralizing the Levi part of a lattice

Module `Langlands.Analysis.FundamentalDomainConjugateTranslation`, namespace
`Langlands.Analysis.LatticeComparison`. Main result: `mul_setLIntegral_mul_left_eq`. Its statement
form is `ConjugateTranslationStatement`, proved by `conjugateTranslation`.

## Statement

The setting is that of `Langlands.Analysis.FundamentalDomainLatticeComparison`, with one lattice:

- `H` and `V` are measurable groups. `μ` is left-invariant and s-finite on `H`; `ν` is left- and
  inversion-invariant and s-finite on `V`.
- `j : V →* H` is measurable and injective.
- `Λ ≤ H` is countable, with a measurable strict fundamental domain `D`.
- `Γ ≤ V` is countable, with `j(Γ) ⊆ Λ`. `C` is a measurable fundamental domain of `Γ`.
- Conjugations `cj l` by elements of `Λ` on `V` preserve `ν` and stabilize `Γ`.
- `e : M × Γ ≃ Λ` with `e(x, γ) = m(x) j(γ)`.

In addition, `a ∈ H` commutes with every `m(x)`, and `α : V ≃* V` satisfies `j(α v) = a j(v) a⁻¹`,
with `α⁻¹` quasi-measure-preserving for `ν`. Then for every measurable `φ ≥ 0` left-invariant under
`Λ` and `j(V)`:

`ν(C) · ∫_D φ(a g) dμ(g) = ν(α(C)) · ∫_D φ dμ`.

The set `α(C)` appears in the Lean statement as `α.symm ⁻¹' C`.

## Proof

- The conjugate lattice `Λ' = aΛa⁻¹` is the image of `Λ` under `MulAut.conj a`. Since `a` commutes
  with `M`, it factors as `M · j(Γ')` with `Γ' = α(Γ)`. The bijection `e'` is the composite of `e`
  with the equivalences `Γ ≃ Γ'` and `Λ ≃ Λ'`.
- `D' = aD` (as the preimage of `D` under `y ↦ a⁻¹ y`) is a strict fundamental domain of `Λ'`.
- `α(C)` is a fundamental domain of `Γ'`, by Mathlib's `IsFundamentalDomain.preimage_of_equiv`,
  which uses quasi-measure-preservation of `α⁻¹`.
- `LatticeComparison.mul_setLIntegral_eq` gives `ν(C) ∫_{aD} φ = ν(α(C)) ∫_D φ`. Left invariance of
  `μ` gives `∫_{aD} φ = ∫_D φ(a ·)`.

## Use and provenance

This is an abstract lemma derived for the proof of Bernstein–Lapid, *On the meromorphic
continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §§7.3–7.5 (pp. 214–217) and the
application of §7.5 to the translations `σ_α` (p. 219). In the intended instance:

- `H = G(𝔸)`, `V = U_P(𝔸)`, `Λ = P₀(F)`, `M = (M_P ∩ P₀)(F)` and `Γ = U_P(F)`.
- `a` is a point of the split component of `P`, which centralizes `M_P`. `α` is conjugation by `a`
  on `U_P(𝔸)`.

The lemma supplies only the unweighted quotient-measure factor. It translates the whole
nonnegative integrand `φ`. If `φ` is itself a weighted integrand, such as `|f|² · w` with
`w = exp(−2⟨λ, H₀(·)⟩)` as in §7.3 (p. 215), then the weight is translated together with `f`.

Translating `f` alone while holding the weight `w` fixed gives a different multiplier. Since
`H₀(a g) = H₀(g) + H₀(a)`, we have `w(g) = exp(2⟨λ, H₀(a)⟩) · w(a g)`. So the squared weighted
norm acquires the additional factor `exp(2⟨λ, H₀(a)⟩)`, on the correspondingly translated domain.
On p. 219 the source accounts for this factor in its constant
`c_α = δ_P(a_α)^{1/2} e^{⟨λ, H₀(a_α)⟩}`; for squared norms the factor is
`δ_P(a_α) e^{2⟨λ, H₀(a_α)⟩}`.

The adelic instantiation, the weight factor and the identification of `ν(aCa⁻¹)` (relative to
`ν(C)`) with the modular character are not part of this module.
