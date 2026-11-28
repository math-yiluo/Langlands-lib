# The trace of a square-integrable representation on a conjugate coefficient

Lean module: `Langlands.BaseChange.CoefficientTraceSchur`.

## Contents

`exists_integral_traceCoefficient_mul_star_coefficient`. Let `F` be a nonarchimedean local
field, `G = GL_n(F)`, `Z` its center, `G ⧸ Z` with its Borel σ-algebra
(`centralQuotientMeasurableSpace`) and `μ` a Haar measure on `G ⧸ Z`. Let `ρ` on `V` and `π`
on `W` be irreducible representations of `G`, square-integrable modulo the center
(`IsSquareIntegrable`), with unitary central characters `cρ`, `cπ` having the same underlying
character, and `d` the formal degree of `π` for `μ` (`IsCentralFormalDegree μ π d`). Let `H` be
a compact open subgroup of `G` fixing `v : W`, and `ℓ` a smooth functional of `π`. Then there is
`T : G ⧸ Z → ℂ` with

`T(gZ) = ψ^ρ_H(g) · conj ℓ(π(g) v)` for all `g`,

`T` is `μ`-integrable, and

`∫_{G/Z} T dμ = d⁻¹ conj ℓ(v)` if `ρ ≅ π`, and `0` otherwise.

Here `ψ^ρ_H = traceCoefficient ρ _ H` is the trace coefficient `g ↦ trace(e_H ρ(g) e_H)` on the
finite-dimensional space `V^H` of `H`-fixed vectors (module
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.TraceCoefficientFamily`), `conj` is complex
conjugation (`star`) and `ρ ≅ π` is `Nonempty (ρ.Equiv π)`. The variables `V` and `W` live in
independent universes, and `F` need not have characteristic zero.

## Mathematical content

The integral is the trace of `ρ(f) = ∫_{G/Z} f(g) ρ(g) dg` for the conjugate coefficient
`f(g) = conj ℓ(π(g) v)`, written through `V^H`. Since `v` is `H`-fixed, `f` is right
`H`-invariant, so `ρ(f) = ρ(f) e_H` and `trace ρ(f) = ∫ ψ^ρ_H f`. Writing `ℓ = ⟨·, w⟩` for an
invariant inner product on `π`, the Schur orthogonality relations give `ρ(f) = 0` if `ρ ≇ π`,
and for `ρ = π` the operator `u ↦ d⁻¹ ⟨u, v⟩ w`, of trace `d⁻¹ ⟨w, v⟩ = d⁻¹ conj ℓ(v)`. This is
the computation by Schur orthogonality in Clozel's proof of Theorem 3 (Clozel 1991, §3,
printed p. 110, PDF p. 121). The Lean proof works with a basis of `V^H` and the functionals of
the dual basis, and never forms the operator `ρ(f)`.

## The proof

1. **Inner product.** `π` is unitarizable (`isUnitarizable_of_isSquareIntegrable`): there is an
   invariant positive Hermitian form `b` on `W`. Every smooth functional of `π` is `⟨·, w⟩` for
   some `w` (`InvariantPositiveForm.toSmoothDual_surjective`); take `w` with `ℓ = ⟨·, w⟩` and
   put `ℓv = ⟨·, v⟩`. Invariance and Hermitian symmetry give
   `conj ℓ(π(g) v) = ℓv(π(g⁻¹) w)`.
2. **Expansion.** Let `β` be a basis of `V^H` and `ℓᵢ` the smooth functional
   `fixedFunctional ρ _ H (β.coord i)` (the `i`-th coordinate composed with the averaging
   projection `e_H`). By `traceCoefficient_eq_sum`, `ψ^ρ_H(g) = Σᵢ ℓᵢ(ρ(g) βᵢ)`, so
   `T = Σᵢ fᵢ` with `fᵢ(gZ) = ℓᵢ(ρ(g) βᵢ) ℓv(π(g⁻¹) w)`, the integrand
   `orthogonalityIntegrand` of Waldspurger's orthogonality relations (module
   `Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchurOrthogonality`). Each `fᵢ` is
   integrable (`integrable_orthogonalityIntegrand`), hence so is `T`, and
   `∫ T = Σᵢ ∫ fᵢ`.
3. **`ρ ≇ π`.** Each `∫ fᵢ` vanishes (`orthogonalityIntegral_eq_zero`).
4. **`ρ ≅ π`.** Fix an equivalence `e : ρ ≅ π`. Transporting `βᵢ` and `ℓᵢ` along `e`, the
   formal degree identity `IsCentralFormalDegree μ π d` gives
   `∫ fᵢ = d⁻¹ ℓv(e βᵢ) ℓᵢ(e⁻¹ w)`. Summing over `i`, the vectors `Σᵢ ℓᵢ(e⁻¹ w) βᵢ` reassemble
   `e_H(e⁻¹ w)`, and `e` intertwines the averaging maps (`Compact.averageMap_commute`), so
   `Σᵢ ℓv(e βᵢ) ℓᵢ(e⁻¹ w) = ℓv(e_H w)`. Since `v` is `H`-fixed and `b` is invariant,
   `ℓv(e_H w) = ⟨w, v⟩ = conj ℓ(v)`. Hence `∫ T = d⁻¹ conj ℓ(v)`.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Source

Laurent Clozel, *Invariant harmonic analysis on the Schwartz space of a reductive p-adic
group*, in Barker and Sally (eds.), *Harmonic Analysis on Reductive Groups*, Progr. Math. 101,
Birkhäuser (1991), §3, proof of Theorem 3 (printed p. 110, PDF p. 121), where
`trace π₁(f) = d(π₁)⁻¹ δ_{π₁, π₂}` for the conjugate coefficient `f` of `π₂` is read off from
the Schur orthogonality relations. Literature ID
`provided-698170812a35ff43dbc4156af9f67a8384f95d97d5836529575e646643af617b`, SHA-256
`c5cb36139e9cf3ed29fe1338a45488236cc69abdc4806d5ba2180456faba08ba`.
