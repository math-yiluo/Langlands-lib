import Langlands.Representation.Archimedean.MaximalParabolicIntegration
import Langlands.Representation.Archimedean.RealLeviChartIntegralStatement
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The `O(N)`-integral in coordinates of a standard parabolic subgroup of `GL_N(ℝ)`

Let `Q` be the upper block triangular parabolic subgroup of `GL_N(ℝ)` with diagonal blocks of
sizes `sz_0, …, sz_{c-1}`, `N̄_Q` its opposite unipotent radical (coordinates
`RealLeviChart.Coord sz`) and `K_M = ∏ᵢ O(sz_i)` the maximal compact subgroup of its Levi factor.
For a smooth function `F` on `GL_N(ℝ)` that transforms on the left by the modulus character of the
upper triangular Borel subgroup, the statement `RealLeviParabolicIntegrationStatement` says
`∫_{O(N)} F = C ∫_{K_M} ∫_{N̄_Q} F(n̄(X) κ) dX dκ` with a constant `C > 0` depending only on the
block sizes. It is only stated here; for two blocks it is the published
`RealBlockParabolicIntegrationStatement`.
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealLeviChart

variable {c : ℕ} (sz : Fin c → ℕ)

/-- The block diagonal matrix `diag(A_0, …, A_{c-1})` in the positions `Fin (∑ i, sz i)`
(Mathlib's `blockDiagonal'` reindexed by `finSigmaFinEquiv`), as a ring homomorphism. -/
def blockDiagHom :
    (∀ i, Matrix (Fin (sz i)) (Fin (sz i)) ℝ) →+* Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ :=
  (Matrix.reindexAlgEquiv ℝ ℝ finSigmaFinEquiv).toRingHom.comp
    (Matrix.blockDiagonal'RingHom (fun i => Fin (sz i)) ℝ)

theorem blockDiagHom_apply (A : ∀ i, Matrix (Fin (sz i)) (Fin (sz i)) ℝ) :
    blockDiagHom sz A = Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv (Matrix.blockDiagonal' A) :=
  rfl

theorem blockDiagHom_pos_pos_self (A : ∀ i, Matrix (Fin (sz i)) (Fin (sz i)) ℝ) (i : Fin c)
    (a b : Fin (sz i)) : blockDiagHom sz A (pos sz i a) (pos sz i b) = A i a b := by
  simp [blockDiagHom_apply, pos, Matrix.blockDiagonal'_apply_eq]

theorem blockDiagHom_pos_pos_of_ne (A : ∀ i, Matrix (Fin (sz i)) (Fin (sz i)) ℝ) {i j : Fin c}
    (hij : i ≠ j) (a : Fin (sz i)) (b : Fin (sz j)) :
    blockDiagHom sz A (pos sz i a) (pos sz j b) = 0 := by
  simp [blockDiagHom_apply, pos, Matrix.blockDiagonal'_apply_ne A a b hij]

/-- `diag(g_0, …, g_{c-1}) ∈ GL_N(ℝ)` for `g_i ∈ GL_{sz_i}(ℝ)`, as a group homomorphism. -/
def blockDiagGL :
    (∀ i, Langlands.GeneralLinear (sz i) ℝ) →* Langlands.GeneralLinear (∑ i, sz i) ℝ :=
  (Units.map (blockDiagHom sz).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom

theorem blockDiagGL_val (g : ∀ i, Langlands.GeneralLinear (sz i) ℝ) :
    ((blockDiagGL sz g : Langlands.GeneralLinear (∑ i, sz i) ℝ) :
      Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) =
      blockDiagHom sz fun i => (g i : Matrix (Fin (sz i)) (Fin (sz i)) ℝ) :=
  rfl

end RealLeviChart

open RealPrincipalSeriesDuality RealLeviChart in
attribute [local instance] measurableSpaceK in
/-- **Statement (integration over `O(N)` in coordinates of a standard parabolic subgroup).** For
all block sizes `sz_0, …, sz_{c-1}` (`N = ∑ sz_i`) there is `C > 0` such that for every smooth
`F : GL_N(ℝ) → ℂ` with `F(diag(z) u g) = ∏ᵢ |zᵢ|^{(N−1) − 2i} F(g)` for upper unipotent `u`
(`MaximalParabolicIntegration.IsModulusCovariant`), and every `κ ∈ K_M = ∏ᵢ O(sz_i)`, the function
`X ↦ F(n̄(X) diag(κ_0, …, κ_{c-1}))` is integrable on the coordinates `Coord sz → ℝ` of the opposite
unipotent radical `N̄_Q` (Lebesgue measure), and
`∫_{O(N)} F = C ∫_{K_M} ∫_{N̄_Q} F(n̄(X) diag(κ_0, …, κ_{c-1})) dX dκ`,
with the Haar probability measures on the orthogonal groups and their product on `K_M`. -/
def RealLeviParabolicIntegrationStatement : Prop :=
  ∀ (c : ℕ) (sz : Fin c → ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ F : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ,
      ContMDiff (matrixModel ℝ (∑ i, sz i)) 𝓘(ℝ, ℂ) ∞ F →
      MaximalParabolicIntegration.IsModulusCovariant F →
      (∀ κ : ∀ i, unitaryCompact ℝ (sz i),
        Integrable fun X : Coord sz → ℝ =>
          F (lowerGL sz X * blockDiagGL sz fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ))) ∧
      ∫ κ, F (κ : Langlands.GeneralLinear (∑ i, sz i) ℝ) ∂haarK (∑ i, sz i) =
        (C : ℂ) * ∫ κ : (∀ i, unitaryCompact ℝ (sz i)),
          (∫ X : Coord sz → ℝ,
            F (lowerGL sz X * blockDiagGL sz fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ)))
          ∂Measure.pi fun i => haarK (sz i)

end Langlands.Archimedean
