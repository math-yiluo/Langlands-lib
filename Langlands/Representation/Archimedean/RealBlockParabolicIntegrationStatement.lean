import Langlands.Representation.Archimedean.MaximalParabolicIntegration

/-!
# The `O(a+k)`-integral in coordinates of the maximal parabolic subgroup `P_{a,k}` of `GL_{a+k}(ℝ)`

For a smooth function `F` on `GL_{a+k}(ℝ)` that transforms on the left by the modulus character
of the upper triangular Borel subgroup, the statement `RealBlockParabolicIntegrationStatement`
says `∫_{O(a+k)} F = c ∫_{O(a)} ∫_{O(k)} ∫_{M_{k×a}(ℝ)} F(n̄(X) diag(κ₁, κ₂)) dX dκ₂ dκ₁` with a
constant `c > 0` depending only on `a, k`, where `n̄(X) = [[1, 0], [X, 1]]`. It is only stated
here; for `k = 1` it is the published `MaximalParabolicIntegrationStatement` (with the variables
reordered).
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealBlockParabolic

variable {a k : ℕ}

/-- `n̄(X) = [[1, 0], [X, 1]]` on `Fin (a + k) = Fin a ⊕ Fin k`. -/
def blockLower (X : Matrix (Fin k) (Fin a) ℝ) : Matrix (Fin (a + k)) (Fin (a + k)) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 X 1)

theorem det_blockLower (X : Matrix (Fin k) (Fin a) ℝ) : (blockLower X).det = 1 := by
  rw [blockLower, Matrix.det_reindex_self,
    Matrix.det_fromBlocks_zero₁₂ (1 : Matrix (Fin a) (Fin a) ℝ) X 1, det_one, det_one, mul_one]

/-- `n̄(X)` as an element of `GL_{a+k}(ℝ)`. -/
def blockLowerGL (X : Matrix (Fin k) (Fin a) ℝ) : Langlands.GeneralLinear (a + k) ℝ :=
  ((Matrix.isUnit_iff_isUnit_det (blockLower X)).mpr (by rw [det_blockLower]; exact isUnit_one)).unit

/-- `diag(A, D)` on `Fin (a + k) = Fin a ⊕ Fin k`. -/
def blockDiag (A : Matrix (Fin a) (Fin a) ℝ) (D : Matrix (Fin k) (Fin k) ℝ) :
    Matrix (Fin (a + k)) (Fin (a + k)) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 D)

theorem det_blockDiag (A : Matrix (Fin a) (Fin a) ℝ) (D : Matrix (Fin k) (Fin k) ℝ) :
    (blockDiag A D).det = A.det * D.det := by
  rw [blockDiag, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂ A 0 D]

/-- `diag(g₁, g₂)` as an element of `GL_{a+k}(ℝ)`. -/
def blockDiagGL (g₁ : Langlands.GeneralLinear a ℝ) (g₂ : Langlands.GeneralLinear k ℝ) :
    Langlands.GeneralLinear (a + k) ℝ :=
  ((Matrix.isUnit_iff_isUnit_det (blockDiag (g₁ : Matrix (Fin a) (Fin a) ℝ)
      (g₂ : Matrix (Fin k) (Fin k) ℝ))).mpr (by
    rw [det_blockDiag]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g₁)).mul
      ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g₂)))).unit

end RealBlockParabolic

open RealPrincipalSeriesDuality RealBlockParabolic in
attribute [local instance] measurableSpaceK in
/-- **Statement (integration over `O(a+k)` in coordinates of `P_{a,k}`).** For all `a, k ∈ ℕ`
there is `c > 0` such that for every smooth `F : GL_{a+k}(ℝ) → ℂ` with
`F(diag(z) u g) = ∏ᵢ |zᵢ|^{(a+k−1) − 2i} F(g)` for upper unipotent `u`
(`MaximalParabolicIntegration.IsModulusCovariant`), and all `κ₁ ∈ O(a)`, `κ₂ ∈ O(k)`, the function
`X ↦ F(n̄(X) diag(κ₁, κ₂))` is integrable on `M_{k×a}(ℝ) = (Fin k → Fin a → ℝ)`, and
`∫_{O(a+k)} F = c ∫_{O(a)} ∫_{O(k)} ∫_{M_{k×a}(ℝ)} F(n̄(X) diag(κ₁, κ₂)) dX dκ₂ dκ₁`,
with the Haar probability measures on the orthogonal groups and Lebesgue measure on
`M_{k×a}(ℝ)`. -/
def RealBlockParabolicIntegrationStatement : Prop :=
  ∀ a k : ℕ, ∃ c : ℝ, 0 < c ∧
    ∀ F : Langlands.GeneralLinear (a + k) ℝ → ℂ,
      ContMDiff (matrixModel ℝ (a + k)) 𝓘(ℝ, ℂ) ∞ F →
      MaximalParabolicIntegration.IsModulusCovariant F →
      (∀ (κ₁ : unitaryCompact ℝ a) (κ₂ : unitaryCompact ℝ k),
        Integrable fun X : Fin k → Fin a → ℝ =>
          F (blockLowerGL (Matrix.of X) *
            blockDiagGL (κ₁ : Langlands.GeneralLinear a ℝ) (κ₂ : Langlands.GeneralLinear k ℝ))) ∧
      ∫ κ, F (κ : Langlands.GeneralLinear (a + k) ℝ) ∂haarK (a + k) =
        (c : ℂ) * ∫ κ₁ : unitaryCompact ℝ a, (∫ κ₂ : unitaryCompact ℝ k,
          (∫ X : Fin k → Fin a → ℝ,
            F (blockLowerGL (Matrix.of X) *
              blockDiagGL (κ₁ : Langlands.GeneralLinear a ℝ) (κ₂ : Langlands.GeneralLinear k ℝ)))
          ∂haarK k) ∂haarK a

end Langlands.Archimedean
