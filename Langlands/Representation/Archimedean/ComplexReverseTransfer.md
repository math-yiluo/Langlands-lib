# Transposing an intertwiner inside a `U(n)`-integral matrix coefficient

Lean module: `Langlands.Representation.Archimedean.ComplexReverseTransfer`, namespace
`Langlands.Archimedean.ComplexReverseTransfer`. Worker 5677 wrote it under Task 7064 as a helper
for `ComplexStrictReverseIntertwinerKernelStatement` (module `ComplexReverseIntertwinerStrict`).

Notation. `GL_n(ℂ)` is `Langlands.GeneralLinear n ℂ`, `U(n)` is `unitaryCompact ℂ n` (as a
subgroup of `GL_n(ℂ)`) or `Matrix.unitaryGroup (Fin n) ℂ`, with Haar probability measure
`ComplexDuality.unitaryHaar n`. `V(χ)` is the space of `U(n)`-finite functions of the principal
series of `χ` (`kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)`), with the
`U(n)`-action `principalSeriesRep ℂ n χ` and the Lie algebra action `principalSeriesLie ℂ n χ`.
`dualChar χ` is the family `z ↦ (χ_l z)⁻¹`; `IsPhasePower χ e` (from `ComplexPartialJacquet`) says
`χ_l(z) = χ_l(z/|z|) (|z|²)^{e_l}`, `χ_l(1) = 1` and `|χ_l(z/|z|)| = 1`. The integration pairing
`integralPairing n χ' χ f h = ∫_{U(n)} f(κ) h(κ) dκ` (module `ComplexDuality.Pairing`) is written
`⟨f, h⟩`. `matrixCoefficient μ a φ g = ∫ a(κ g) φ(κ) dμ(κ)` is the Library definition of
`ComplexMatrixCoefficientAnalytic`.

## Results

- `exists_pairing_transpose` (the pairing transpose). Let `IsPhasePower χ e` and
  `T : V(χ) → V(ψ)` be `ℂ`-linear and `U(n)`-equivariant. For every `v ∈ V(dualChar ψ)` there is
  `u ∈ V(dualChar χ)` with `⟨u, h⟩ = ⟨v, T h⟩` for all `h ∈ V(χ)`.
- `matrixCoefficient_eq_of_rel` (equality of matrix coefficients from equality at `1`). Let `χ₁`,
  `χ₂` satisfy `χ_i l z = χ_i l (z/|z|) (|z|²)^{e_i l}`, `μ` a finite measure on `U(n)` and
  `φ₁, φ₂` continuous on `U(n)`. Let `P` be a relation between functions on `GL_n(ℂ)` such that
  `P a b` implies `a ∈ V(χ₁)` and `b ∈ V(χ₂)`, which is stable under right translation of both
  sides by `k ∈ U(n)` and under applying the same right derivative `R(X)` (`X` any complex
  `n × n` matrix) to both sides. If `matrixCoefficient μ a φ₁ 1 = matrixCoefficient μ b φ₂ 1`
  whenever `P a b`, then `matrixCoefficient μ a φ₁ g = matrixCoefficient μ b φ₂ g` for all `g`
  whenever `P a b`.
- `toUnits_mk`: the inclusion `Matrix.unitaryGroup → GL_n(ℂ)` sends `⟨k, hk⟩` to `k`.
- `integral_mul_transfer` (the transfer identity). Let `IsPhasePower χ eχ`, `IsPhasePower ψ eψ`,
  `T : V(χ) → V(ψ)` linear and commuting with the `U(n)`-actions and with the actions of
  `1 ⊗ X` for every complex matrix `X`. Let `v ∈ V(dualChar ψ)` and `u ∈ V(dualChar χ)` with
  `⟨u, h⟩ = ⟨v, T h⟩` for all `h`. Then for every `w ∈ V(χ)` and `g ∈ GL_n(ℂ)`
  `∫_{U(n)} (T w)(κ g) v(κ) dκ = ∫_{U(n)} w(κ g) u(κ) dκ`.

## Proof

- `exists_pairing_transpose` follows `ComplexStandardHomTransposeProof.exists_transpose` with `T`
  composed in. The map `Λ : V(dualChar ψ) → V(χ)*`, `Λ f = ⟨f, T ·⟩`, is `U(n)`-equivariant into
  the dual representation (pairing invariance `integralPairing_principalSeriesRep` and
  equivariance of `T`), so `Λ v` is a `U(n)`-finite vector of the dual
  (`isFiniteVector_dual_of_equivariant`). The range of `Qd : V(dualChar χ) → V(χ)*`,
  `Qd f = ⟨f, ·⟩`, is a subrepresentation of `U(n)`-finite vectors which separates `V(χ)`
  (`exists_integralPairing_ne_zero_left`; its hypothesis on norms is
  `Complex.normSq ((χ_l z)⁻¹) = (Complex.normSq z)^{-2 Re e_l}`,
  `ComplexJacquetKernel.normSq_dualChar`). Since `V(χ)` is admissible and `U(n)`-semisimple,
  `KFiniteDual.mem_of_separating` puts `Λ v` in this range: `Λ v = Qd u`.
- `matrixCoefficient_eq_of_rel`. First, along `t ↦ g expDiag(h, t)` (with
  `expDiag(h, t) = diag(e^{t h_j})`) for a fixed `g` at which all related pairs agree: both
  matrix coefficients are real analytic in `t` (`analyticAt_matrixCoefficient`), and the
  derivative of `t ↦ matrixCoefficient μ a φ₁ (g expDiag(h, t))` is the matrix coefficient of
  `R(diag h) a`. As `P` is stable under `R(diag h)` on both sides, all derivatives of the
  difference vanish at `t = 0`, so the difference vanishes identically
  (`MatrixCoefficientAnalytic.eq_zero_of_iteratedDeriv_eq_zero`). Then for general `g`, write
  `g = k₁ expDiag(h, 1) k₂` (`exists_kak`). Right translation by `k₂` is absorbed in the
  functions (`matrixCoefficient_mul_unitary`, stability of `P` under `U(n)`), and agreement at
  `k₁` follows from agreement at `1` for the translated pair. The first step applied at `k₁`
  gives agreement at `k₁ expDiag(h, 1)`.
- `integral_mul_transfer`: apply `matrixCoefficient_eq_of_rel` with
  `μ = (unitaryHaar n).map toUnitaryGroup`, `φ₁ = v`, `φ₂ = u` and the relation
  `P a b :⇔ ∃ w', a = T w' ∧ b = w'`. Its stability under `U(n)` and `R(X)` is the
  `(𝔤, K)`-equivariance of `T` (`principalSeriesRep_apply_coe`,
  `principalSeriesLie_one_tmul_apply_coe`). At `g = 1` the two matrix coefficients are
  `⟨v, T w'⟩` and `⟨u, w'⟩` (up to the order of the factors), equal by hypothesis. The
  matrix coefficients for `μ` are the `unitaryHaar` integrals of the statement
  (`ComplexJacquetDual.integral_map_toUnitaryGroup`).

## Provenance

Derived (internal). `exists_pairing_transpose` adapts the Library proof
`ComplexStandardHomTransposeProof.exists_transpose`; `matrixCoefficient_eq_of_rel` is the
standard real-analyticity argument for matrix coefficients of `U(n)`-finite vectors (as in the
Library module `ComplexMatrixCoefficientAnalytic`), stated for a relation between two families.
No statement from the literature is introduced; all results are proved here.
