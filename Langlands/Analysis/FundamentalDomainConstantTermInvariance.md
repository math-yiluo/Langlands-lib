# Invariance of the folded constant term

Module `Langlands.Analysis.FundamentalDomainConstantTermInvariance`, namespace
`Langlands.Analysis.FibreAverage`. Main results: `foldConstantTerm_mul_left` and
`foldConstantTerm_mul_left_j`. Their statement form is `FoldConstantTermInvarianceStatement`,
proved by `foldConstantTermInvariance`.

## Statement

The setting is that of `foldConstantTerm` (module
`Langlands.Analysis.FundamentalDomainConstantTermL2`):

- `Λ ≤ H` is countable, with a strict fundamental domain `D` (`hD`).
- `j : V →* H` is injective.
- `Γ ≤ V` is countable, with `j(Γ) ⊆ Λ`.
- Conjugations `cj l` satisfy `j(cj l v) = l j(v) l⁻¹`, preserve `ν` and stabilize `Γ`.
- `ν` is a left- and right-invariant measure on `V`, and `C` is a fundamental domain of `Γ`.

Recall
`foldConstantTerm Λ D hD j ν C f g = ν(C)⁻¹ ∫_C f(fold(j(v) g)) dν(v)`,
where `fold x` is the unique `Λ`-translate of `x` in `D`. For every function `f : H → ℂ` and every
`g ∈ H`:

1. `foldConstantTerm … f (l g) = foldConstantTerm … f g` for every `l ∈ Λ`.
2. `foldConstantTerm … f (j(w) g) = foldConstantTerm … f g` for every `w ∈ V`.

These hold at every point, with no measurability or integrability hypothesis. If the integrand is
not integrable, both sides are computed with Bochner's convention.

## Proof

- Helper lemmas `cj_inv_cj'`, `cj_mul'` and `isFundamentalDomain_preimage_cj'` come from
  injectivity of `j`. They restate private lemmas of `FundamentalDomainFibreAverage`.
- For item 1, write `j(v) l g = l · j(cj l⁻¹ v) g`, and use `fold(l x) = fold(x)`. Change variables
  by the measure-preserving bijection `cj l⁻¹`. This turns the integral into an integral of
  `ψ(v) = f(fold(j(v) g))` over the fundamental domain `cj l⁻¹(C)`. Since `ψ` is `Γ`-invariant
  (`j(Γ) ⊆ Λ`), Mathlib's `IsFundamentalDomain.setIntegral_eq` gives the integral over `C`.
- For item 2, `j(v) j(w) g = j(v w) g`. Change variables by right multiplication with `w`, which
  preserves `ν` by right invariance. `C w` is a fundamental domain of `Γ`, and
  `IsFundamentalDomain.setIntegral_eq` applies again.

## Use and provenance

This is a derived lemma for the weighted `L²` constant-term operators of the proof of
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37
(2024), 187–234, registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §7.3
(p. 214). There `CT_P f` is a function on `P₀(F)U_P(𝔸)\G(𝔸)`. In the adelic instance (`Λ = P₀(F)`,
`V = U_P(𝔸)`), the lemma says that the folded constant term of any representative is everywhere
invariant under `P₀(F)` and `U_P(𝔸)`. This is the canonical representative needed to apply the
split-component translations to classes in the image of the constant-term operator.
