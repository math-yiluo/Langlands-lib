# Dual transforms of coefficients and of spherical Whittaker functions

This internal auxiliary module identifies the two dual transforms that appear
in the dual zeta integral of Jacquet, Piatetski-Shapiro and Shalika
(JPSS 1981, §4, display (3) of (4.2)) when the second function is Jacquet's
spherical Whittaker function `W(g; x; ψ̄)`. It uses the published first identity
and proves the remaining two:

1. the first dual transform of a coefficient of `π` for a functional `ℓ` is the
   coefficient of the same vector for the dual functional of the
   inverse-transpose pullback of `π`;
2. Schur functions at inverse parameters: `s_lam(x⁻¹) = s_(-w₀ lam)(x)` for
   every antitone weight `lam` and every `x : Fin (n + 1) → ℂˣ`, repeated
   parameters included;
3. the second dual transform of `W(g; x; ψ̄)` is `W(g; x⁻¹; ψ)`, the spherical
   Whittaker function attached to the additive character `ψ.scale (-1)` at the
   inverse parameters.

It introduces one definition, `dualWeight`, the weight `-w₀ lam`. All other
declarations are theorems about published Library definitions. No hypothesis
of the module is analytic: the identities are pointwise equalities of
functions on the group.

## The first dual transform of a coefficient

The imported `Langlands.RankinSelberg.firstDualFunction_coefficient ψ π ℓ v` proves, for a field `F` with a
topological-ring structure, a unitary additive character `ψ`, a complex
representation `π` of `GeneralLinear (n + 1) F` and `ℓ : glFunctionals ψ n π`:

`firstDualFunction ψ n (coefficientMap π ℓ v) = coefficientMap (inverseTransposePullback π) (scaledDualFunctional ψ π ℓ) v`.

The published `firstDualFunction` is `W ↦ (g ↦ W(w₀ ᵗg⁻¹))` with `w₀ =
weylLong`. The coefficient of `v` is `g ↦ ℓ(π(g) v)`. Its first dual is
`g ↦ ℓ(π(w₀ ᵗg⁻¹) v) = ℓ(π(w₀)(π(ᵗg⁻¹) v))`, which is the coefficient of `v` in
the representation `g ↦ π(ᵗg⁻¹)` for the functional `ℓ ∘ π(w₀)`. The latter
is the published `dualFunctional`, transported to `ψ.scale (-1)` as
`scaledDualFunctional` (from `EssentialDualSetup`), which is defined as the
published `firstDualFunctional`. The existing theorem supplies this same identity;
this module declares no duplicate coefficient lemma.

## Cells, the long Weyl element and torus elements

Here `F` is a field with a valuation `v` with values in a linearly ordered
commutative group with zero, and `ϖ` is a uniformizing element.

- `cellFunction_congr`: the published `cellFunction hϖ θ c` depends on the
  coefficient family `c` only through its values at antitone exponents.
- `weylLong_mem_integralSubgroup_of_valuation`: `w₀` lies in `GL_(n+1)(O)`
  (its entries and the entries of its inverse are `0` or `1`).
- `inverseTranspose_mem_integralSubgroup_of_valuation`: `k ↦ ᵗk⁻¹` preserves
  `GL_(n+1)(O)` (entries of `ᵗk⁻¹` are entries of `k⁻¹`, and conversely).
- `weylLong_mul_torus_mul_weylLong`: `w₀ ϖ^lam w₀ = ϖ^(i ↦ lam(n - i))`.
- `inverseTranspose_torus_eq`: `ᵗ(ϖ^lam)⁻¹ = ϖ^(-lam)`.

## Reversed and negated weights

`dualWeight lam` is the weight `i ↦ -lam(n - i)` (written with `Fin.rev`),
that is `-w₀ lam`. `antitone_dualWeight_iff` proves that it is antitone exactly
when `lam` is. `halfModulus_dualWeight` proves that the published
`halfModulus q` (the value of `δ_B^(1/2)` at `ϖ^lam`, namely
`(√q)^(-Σ_i (n - 2i) lam i)`) takes the same value at `dualWeight lam` and at
`lam`: reindexing by `i ↦ n - i` turns `Σ_i (n - 2i) (-lam(n - i))` into
`Σ_i (n - 2i) lam i`.

## Schur functions at inverse parameters

The published `satakeSchur x lam` is
`(∏ x_k)^(lam n) · s_α(x)` with `α i = lam i - lam n` nonnegative and antitone,
and `s_α` the evaluation of the published Jacobi–Trudi polynomial
`jacobiTrudi ℂ α`. The published `jacobiTrudi_mul_baseAlternant`
(`RankinSelberg/SymmetricAlternantBridge`) is the bialternant formula
`s_α · a_0 = a_α`, where `a_γ` is the determinant of
`alternantMatrix ℂ γ = (X_k^(γ_i - i + n))_(i,k)` (exponents nonnegative for
the antitone nonnegative weights used here).

- `sign_mul_eval_inv_alternant`: for nonnegative antitone `γ` and nonzero
  `y_k`, `sgn(rev) · (∏ y_k)^(γ 0 + n) · a_γ(y⁻¹) = a_(γ')(y)` with
  `γ' i = γ 0 - γ(n - i)`. Multiplying column `k` of the evaluated alternant
  at `y⁻¹` by `y_k^(γ 0 + n)` gives the matrix `(y_k^(γ 0 - γ i + i))`
  (`Matrix.det_mul_row`), and reversing its rows gives the alternant of `γ'`
  at `y` (`Matrix.det_permute`).
- `jacobiTrudi_inv_mul_baseAlternant`: the cross-multiplied identity
  `(∏ y_k)^(α 0) s_α(y⁻¹) a_0(y) = s_β(y) a_0(y)` with
  `β i = α 0 - α(n - i)`, a linear combination of the previous item for `α`
  and for `0` and of the bialternant formula for `α` (at `y⁻¹`) and for `β`
  (at `y`).
- `prod_zpow_mul_eval_inv_jacobiTrudi`: `(∏ x_k)^(α 0) s_α(x⁻¹) = s_β(x)` for
  every `x : Fin (n + 1) → ℂˣ`. The left side is the evaluation of an element
  `f` of the published Laurent polynomial algebra `TorusPolynomialAlgebra`
  (the localization of `MvPolynomial` at `∏ X_k`), which is a domain. The
  previous item holds at every point of the torus, so
  `torusPolynomial_eq_of_evaluations` gives `f · a_0 = s_β · a_0` in that
  algebra. The base alternant `a_0` is nonzero there (it is the determinant of
  the published `erasedCoefficientMatrix`, nonzero by
  `det_erasedCoefficientMatrix_ne_zero`), so it cancels, and evaluating at `x`
  gives the identity. This step needs no assumption that the `x_k` are
  distinct.
- `satakeSchur_inv`: for antitone `lam` and every `x : Fin (n + 1) → ℂˣ`,
  `satakeSchur x⁻¹ lam = satakeSchur x (dualWeight lam)`. With
  `α i = lam i - lam n`, the weight `β` of the previous item is
  `i ↦ dualWeight lam i - dualWeight lam n`, and the powers of `∏ x_k` agree
  because `-lam n - (lam 0 - lam n) = -lam 0 = dualWeight lam n`.

This is the classical identity `s_λ(x⁻¹) = s_(-w₀λ)(x)` for the characters of
`GL_(n+1)(ℂ)` (the character of the contragredient), proved here directly from
the bialternant formula.

## The second dual transform of the spherical Whittaker function

Now `F` carries `ValuativeRel F` and a topological-ring structure, `ψ` is
trivial on the valuation integers (`hψ`), `ϖ` is a uniformizing element and
`q : ℕ`. The published `inverseSphericalWhittaker hψ hϖ q x` is Jacquet's
`W(g; x; ψ̄)`: the spherical function `sphericalWhittaker hϖ θ q x` for the
inverse standard character `θ` of `ψ`, viewed in the Whittaker space of that
character. It is right `GL_(n+1)(O)`-invariant and its value at `ϖ^lam` is
`δ_B^(1/2)(ϖ^lam) s_lam(x)` for antitone `lam` and `0` otherwise
(`sphericalWhittaker_torus`).

- `secondDualFunction_inverseSphericalWhittaker_torus`: the published
  `secondDualFunction ψ n` sends `W` to `g ↦ W(w₀ ᵗg⁻¹)`. At `g = ϖ^lam` this
  is `W(w₀ ϖ^(-lam)) = W(ϖ^(dualWeight lam) w₀)`, which equals
  `W(ϖ^(dualWeight lam))` by right `GL_(n+1)(O)`-invariance and the
  integrality of `w₀`. By the torus formula, `antitone_dualWeight_iff`,
  `halfModulus_dualWeight` and `satakeSchur_inv`, the value is
  `δ_B^(1/2)(ϖ^lam) s_lam(x⁻¹)` for antitone `lam` and `0` otherwise.
- `secondDualFunction_inverseSphericalWhittaker`: given also `hψ'`, triviality
  of `ψ.scale (-1)` on the valuation integers,
  `secondDualFunction ψ n (inverseSphericalWhittaker hψ hϖ q x) = inverseSphericalWhittaker hψ' hϖ q x⁻¹`.
  The inverse standard character of `ψ.scale (-1)` is the standard character
  of `ψ`, which is the equivariance character of the second dual transform.
  The proof applies the published uniqueness `eq_cellFunction`: the left side
  is right `GL_(n+1)(O)`-invariant (by
  `inverseTranspose_mem_integralSubgroup_of_valuation` and invariance of
  `W(·; x; ψ̄)`), vanishes at non-antitone torus elements, and so equals the
  cell function of its torus values; `cellFunction_congr` and the previous
  item identify that cell function with the defining one of
  `sphericalWhittaker` at `x⁻¹`.

## Provenance

These are internal supporting results for Task 5777 (the corank-one spherical
functional equation for all Satake parameters). They make explicit, for the
Library's definitions, the identifications used without comment in JPSS 1981,
§4: the dual integral of a coefficient of `π` is a zeta integral of a
coefficient of the contragredient realized on `π ∘ (g ↦ ᵗg⁻¹)`, and the dual of
`W(·; x; ψ̄)` is the spherical Whittaker function at the inverse parameters.
The proofs use only published Library definitions and lemmas and Mathlib.
