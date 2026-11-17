# The degree of an endomorphism is a determinant: setup and polynomial identities

This module sets up the algebraic part of Milne's proof of Proposition 12.9 (*Abelian Varieties*, author revision 2022, pp. 21–24) and proves the polynomial identities it needs. The conclusion `DegreeData.det_eq` is in the module `DetComparison`.

## Definitions

All names are in the namespace `Langlands.Algebra.DegreeDeterminant`.

- `ofCoeffs x`: the polynomial `∑_{i < n} x_i X^i` with coefficient vector `x : Fin n → S`. Lemmas: `coeff_ofCoeffs`, `coeff_ofCoeffs_fin`, `ofCoeffs_coeff` (a polynomial of degree `< n` is `ofCoeffs` of its first `n` coefficients), `natDegree_ofCoeffs_lt`, `map_ofCoeffs`, `ofCoeffs_update`, `ofCoeffs_single_zero`, `map_ofCoeffs_X`.
- `DegreeData ρ δ iso` (a `Prop`-valued structure): `R` is a ring, `ρ : R →+* Matrix (Fin (2 * g)) (Fin (2 * g)) ℚ_[p]`, `δ : R → ℚ` and `iso : R → Prop`. The four fields are:
  - `line`: for all `φ ψ` there is `P : ℚ[X]` of degree at most `2 * g` with `δ (n • φ + ψ) = P.eval n` for all `n : ℕ`;
  - `mul`: `δ (β * γ) = δ β * δ γ` when `iso β` and `iso γ`;
  - `norm`: `‖(δ β : ℚ_[p])‖ = ‖(ρ β).det‖` when `iso β`;
  - `zero`: `(ρ β).det = 0` when not `iso β`.

  These are the inputs of Milne's argument. For an abelian variety, `δ` is the degree, `iso` is being an isogeny, and `ρ` is the matrix of the `p`-adic Tate map.
- `coeffEval M F`: for `M : MvPolynomial (Fin n) ℚ` and `F` over a `ℚ`-algebra `S`, the value of `M` at the first `n` coefficients of `F`.
- `edet A y`: for a matrix `A` over `ℚ_[p]` and a coefficient vector `y` over a `ℚ_[p]`-algebra `T`, the determinant of `∑_k y_k • A^k`, that is, of `F(A)` with `F = ofCoeffs y` (`edet_eq`).
- `linePt M` and `lineQ M = (linePt M).comp (-X)`: the one-variable polynomials `x ↦ coeffEval M (C x + X)` and `x ↦ coeffEval M (X - C x)`.

## Results

Fix `hD : DegreeData ρ δ iso`, `α : R`, `N = 2 * (2 * g + 1) + 1`, and `M : MvPolynomial (Fin N) ℚ` with `δ (aeval α (ofCoeffs x)) = M(x)` for all `x : Fin N → ℕ`.

- `DegreeData.exists_mvPolynomial`: such an `M` exists, for any `n` in place of `N`. The proof applies `exists_mvPolynomial_of_line` (module `LineInterpolation`) to `x ↦ δ(F_x(α))`, using `line` with `φ = α ^ i`.
- `DegreeData.iso_of_det_ne_zero`, `ρ_aeval` (`ρ` commutes with evaluation of natural-coefficient polynomials), `edet_natCast` (at natural points, `edet (ρ α) x` is `det ρ(F_x(α))`), `coeffEval_natCast` (at natural-coefficient `G` of degree `< N`, `coeffEval M G = δ (aeval α G)`), `coeffEval_map` and `algebraMap_eval` (compatibility with `ℚ`-algebra maps), `map_edet`.
- `eq_of_eval_natCast_of_ne_zero` (transfer): two rational multivariate polynomials that agree at the natural-number points where a nonzero polynomial `Z` over a characteristic-zero field does not vanish are equal. The proof applies `MvPolynomial.funext_set` to `(Ψ₁ - Ψ₂) · Z` on the box of natural numbers.
- `coeffEval_mul` (multiplicativity): over every `ℚ`-algebra `S`, `coeffEval M (F * G) = coeffEval M F * coeffEval M G` when `F` and `G` have degree at most `2g + 1`. The identity is first proved for generic polynomials `𝔽 = ofCoeffs (X ∘ inl)` and `𝔾 = ofCoeffs (X ∘ inr)` with rational multivariate coefficients, by the transfer lemma with `Z = edet (X ∘ inl) · edet (X ∘ inr)`. At a natural point where `Z ≠ 0`, both factors are isogenies by `zero`, so `mul` applies. `Z ≠ 0` because its value at the coefficient vectors of `1, 1` is `1`. The identity is then specialized.
- `eval_natCast_eq_pow_of_mul`, `det_natCast`, `DegreeData.δ_natCast`: `δ (n : R) = n ^ (2g)` for `n ≥ 1`. The line polynomial `P` of `n ↦ δ(n • 1)` is multiplicative on positive integers. Comparing leading coefficients of `P(mX)` and `P(m) P(X)` gives `P(m) = m ^ j` with `j = natDegree P`. Then `norm` at `β = p` gives `‖p‖ ^ j = ‖p‖ ^ (2g)`, so `j = 2g`.
- `coeffEval_C_eq` and `coeffEval_C`: `coeffEval M (C c) = c ^ (2g)` over every `ℚ`-algebra.
- `coeffEval_line_eq` and `coeffEval_X_sub_C`: `coeffEval M` on lines is given by `linePt` and `lineQ`.
- `linePt_monic` and `lineQ_monic`: `linePt M` and `lineQ M` are monic of degree `2g`. The degree bound for `linePt M` comes from `line` with `φ = 1, ψ = α`. For `R₁(y) = coeffEval M (C 1 + C y * X)` it comes from `line` with `φ = α, ψ = 1`, and `R₁(0) = 1`. Multiplicativity with a constant gives `linePt(x) = x ^ (2g) R₁(1/x)`, so `linePt M = reflect (2g) R₁` and its coefficient of degree `2g` is `R₁(0) = 1`.

## Provenance

Milne, *Abelian Varieties*, author revision 2022: the degree function and its multiplicativity (p. 21), Proposition 12.4 (degree is a polynomial function of degree `2g`), the characteristic polynomial `P_α` (p. 23, "P_α is monic"), and the proof of Proposition 12.9 (pp. 23–24). The structure `DegreeData` isolates the hypotheses that proof uses. Milne extends `deg` to all of `End⁰(A)` and uses multiplicativity there. Here multiplicativity holds only on isogenies and the polynomial identities are obtained by Zariski density (`eq_of_eval_natCast_of_ne_zero`). This route is internal. It is needed because `δ` is not assumed to vanish on non-isogenies.
