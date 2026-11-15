import Langlands.Representation.Archimedean.ComplexKIntegralInvariance

/-!
# The `U(a+k)`-integral in coordinates of the maximal parabolic subgroup `P_{a,k}` of `GL_{a+k}(ℂ)`

For `F` in the smooth principal series of `GL_{a+k}(ℂ)` of the modulus character of the upper
triangular Borel subgroup, the statement `ComplexBlockParabolicIntegrationStatement` says
`∫_{U(a+k)} F = c ∫_{U(a)} ∫_{U(k)} ∫_{M_{k×a}(ℂ)} F(n̄(X) diag(κ₁, κ₂)) dX dκ₂ dκ₁` with a constant
`c > 0` depending only on `a, k`, where `n̄(X) = [[1, 0], [X, 1]]`. It is only stated here; for
`k = 1` it is `ComplexMaximalParabolicIntegration.integral_eq_chart` (with the variables reordered).
-/

noncomputable section

open MeasureTheory Matrix

namespace Langlands.Archimedean

set_option autoImplicit false

namespace ComplexBlockParabolic

variable {a k : ℕ}

/-- `n̄(X) = [[1, 0], [X, 1]]` on `Fin (a + k) = Fin a ⊕ Fin k`. -/
def blockLower (X : Matrix (Fin k) (Fin a) ℂ) : Matrix (Fin (a + k)) (Fin (a + k)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 X 1)

theorem det_blockLower (X : Matrix (Fin k) (Fin a) ℂ) : (blockLower X).det = 1 := by
  rw [blockLower, Matrix.det_reindex_self,
    Matrix.det_fromBlocks_zero₁₂ (1 : Matrix (Fin a) (Fin a) ℂ) X 1, det_one, det_one, mul_one]

/-- `n̄(X)` as an element of `GL_{a+k}(ℂ)`. -/
def blockLowerGL (X : Matrix (Fin k) (Fin a) ℂ) : Langlands.GeneralLinear (a + k) ℂ :=
  ((Matrix.isUnit_iff_isUnit_det (blockLower X)).mpr (by rw [det_blockLower]; exact isUnit_one)).unit

/-- `diag(A, D)` on `Fin (a + k) = Fin a ⊕ Fin k`. -/
def blockDiag (A : Matrix (Fin a) (Fin a) ℂ) (D : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin (a + k)) (Fin (a + k)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 D)

theorem det_blockDiag (A : Matrix (Fin a) (Fin a) ℂ) (D : Matrix (Fin k) (Fin k) ℂ) :
    (blockDiag A D).det = A.det * D.det := by
  rw [blockDiag, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂ A 0 D]

/-- `diag(g₁, g₂)` as an element of `GL_{a+k}(ℂ)`. -/
def blockDiagGL (g₁ : Langlands.GeneralLinear a ℂ) (g₂ : Langlands.GeneralLinear k ℂ) :
    Langlands.GeneralLinear (a + k) ℂ :=
  ((Matrix.isUnit_iff_isUnit_det (blockDiag (g₁ : Matrix (Fin a) (Fin a) ℂ)
      (g₂ : Matrix (Fin k) (Fin k) ℂ))).mpr (by
    rw [det_blockDiag]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g₁)).mul
      ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g₂)))).unit

end ComplexBlockParabolic

open ComplexDuality ComplexBlockParabolic in
/-- **Statement (integration over `U(a+k)` in coordinates of `P_{a,k}`).** For all `a, k ∈ ℕ`
there is `c > 0` such that for every `F` in the smooth principal series of `GL_{a+k}(ℂ)` of the
modulus character `modulusCharacter (a + k)` (the functions with
`F(diag(z) u g) = ∏ᵢ |zᵢ|^{2((a+k−1) − 2i)} F(g)`, `u` upper unipotent), and all `κ₁ ∈ U(a)`,
`κ₂ ∈ U(k)`, the function `X ↦ F(n̄(X) diag(κ₁, κ₂))` is integrable on
`M_{k×a}(ℂ) = (Fin k → Fin a → ℂ)`, and
`∫_{U(a+k)} F = c ∫_{U(a)} ∫_{U(k)} ∫_{M_{k×a}(ℂ)} F(n̄(X) diag(κ₁, κ₂)) dX dκ₂ dκ₁`,
with the Haar probability measures on the unitary groups and Lebesgue measure on `M_{k×a}(ℂ)`. -/
def ComplexBlockParabolicIntegrationStatement : Prop :=
  ∀ a k : ℕ, ∃ c : ℝ, 0 < c ∧
    ∀ F ∈ principalSeries ℂ (a + k) (ComplexKIntegralInvariance.modulusCharacter (a + k)),
      (∀ (κ₁ : unitaryCompact ℂ a) (κ₂ : unitaryCompact ℂ k),
        Integrable fun X : Fin k → Fin a → ℂ =>
          F (blockLowerGL (Matrix.of X) *
            blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear k ℂ))) ∧
      ∫ κ, F (κ : Langlands.GeneralLinear (a + k) ℂ) ∂unitaryHaar (a + k) =
        (c : ℂ) * ∫ κ₁ : unitaryCompact ℂ a, (∫ κ₂ : unitaryCompact ℂ k,
          (∫ X : Fin k → Fin a → ℂ,
            F (blockLowerGL (Matrix.of X) *
              blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear k ℂ)))
          ∂unitaryHaar k) ∂unitaryHaar a

end Langlands.Archimedean
