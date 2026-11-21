import Langlands.Global.RankinSelberg.ComplexLocalAdjacentJacquetExpansion
import Langlands.Global.RankinSelberg.ComplexLocalEqualMeromorphicReduction
import Langlands.Global.RankinSelberg.ComplexLocalFourierSchwartz
import Langlands.Global.RankinSelberg.ComplexLocalOrdinaryConvergence
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerDual

/-! # Absolute convergence of the four endpoint integrals in the Jacquet induction -/

noncomputable section

open MeasureTheory Langlands.LocalFactor.Archimedean
open scoped Manifold ContDiff Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal ComplexLocalConvergence
open ComplexCharacterChange (model_pair_invariant)
open ComplexLocalWhittakerDual (dualData dualFunction_mem)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "H" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G" => Langlands.GeneralLinear (r + 2) ℂ
local notation "Row" => Fin (r + 1) → ℂ
local notation "gap" => Nat.lt_succ_self r

private theorem exists_integrable_equal {ds es : List ComplexCharacterData}
    (hd : ds.length = r + 1) (he : es.length = r + 1)
    {a : ℂˣ} {W V : H → ℂ} (hW : W ∈ complexWhittakerModel r ds a)
    (hV : V ∈ complexWhittakerModel r es (-a))
    (D : ComplexQuotientMeasureData r) (Φ : 𝓢(Row, ℂ)) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Integrable (complexEqualIntegrand W V Φ s) D.measure := by
  have hB := complexLocalWhittakerSimpleRootBound_of_uniformGrowth complexLocalWhittakerUniformGrowth
  have hrow : Continuous (Langlands.RankinSelberg.lastRow : H → Row) :=
    continuous_pi fun j => (GeneralLinear.entry (R := ℂ) (Fin.last r) j).continuous
  exact exists_integrable_complexEqualIntegrand_of_logarithmicKernelBound D
    (model_pair_invariant hW hV)
    (((contMDiff_of_mem_complexWhittakerModel hW).continuous.mul
      (contMDiff_of_mem_complexWhittakerModel hV).continuous).mul (Φ.continuous.comp hrow))
    (hasLogarithmicKernelBound_of_simpleRoots (hB r ds hd a W hW) (hB r es he (-a) V hV) Φ)

/-- Convergence on a common right half-plane for the two equal-rank endpoint kernels. -/
theorem complexLocalEqualEndpointConvergence {ds es : List ComplexCharacterData}
    (hd : ds.length = r + 1) (he : es.length = r + 1) (a : ℂˣ)
    (D : ComplexQuotientMeasureData r) (W V : H → ℂ) (Φ : 𝓢(Row, ℂ))
    (hW : W ∈ complexWhittakerModel r ds a) (hV : V ∈ complexWhittakerModel r es (-a)) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (complexEqualIntegrand W V Φ s) D.measure ∧
      Integrable (complexEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
        (ArchimedeanLocal.dualFunction (r + 1) V) (complexFourierTransform a Φ) s) D.measure := by
  obtain ⟨Φd, hΦd⟩ := exists_schwartz_complexFourierTransform a Φ
  obtain ⟨σ, hσ⟩ := exists_integrable_equal hd he hW hV D Φ
  obtain ⟨τ, hτ⟩ := exists_integrable_equal ((ComplexLocalWhittakerDual.length_dualData _).trans hd)
    ((ComplexLocalWhittakerDual.length_dualData _).trans he)
    (dualFunction_mem hd hW) (dualFunction_mem he hV) D Φd
  refine ⟨max σ τ, fun s hs => ⟨hσ s ((le_max_left _ _).trans_lt hs), ?_⟩⟩
  rw [← hΦd]
  exact hτ s ((le_max_right _ _).trans_lt hs)

/-- Convergence on a common right half-plane for the two corank-one endpoint kernels. -/
theorem complexLocalAdjacentEndpointConvergence {ds es : List ComplexCharacterData}
    (hd : ds.length = r + 2) (he : es.length = r + 1) (a : ℂˣ)
    (D : ComplexQuotientMeasureData r) (W : G → ℂ) (V : H → ℂ)
    (hW : W ∈ complexWhittakerModel (r + 1) ds a) (hV : V ∈ complexWhittakerModel r es (-a)) :
    HasAdjacentJacquetConvergence a D W V := by
  obtain ⟨σ, hσ⟩ := complexLocalOrdinaryConvergence gap ds es a D ⟨W, hW⟩ ⟨V, hV⟩
  obtain ⟨τ, hτ⟩ := complexLocalOrdinaryConvergence gap (dualData ds) (dualData es) (-a) D
    ⟨_, dualFunction_mem hd hW⟩ ⟨_, dualFunction_mem he hV⟩
  exact ⟨max σ τ, fun s hs => ⟨hσ s ((le_max_left _ _).trans_lt hs),
    (integrable_complexUnequalDualKernel_adjacent_iff a D W V s).mpr
      (hτ s ((le_max_right _ _).trans_lt hs))⟩⟩

/-- Both convergence packages used at the two steps of the complex Jacquet induction. -/
def ComplexLocalJacquetEndpointConvergenceStatement : Prop :=
  (∀ (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = r + 1 →
    ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r) (W V : H → ℂ) (Φ : 𝓢(Row, ℂ)),
    W ∈ complexWhittakerModel r ds a → V ∈ complexWhittakerModel r es (-a) →
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (complexEqualIntegrand W V Φ s) D.measure ∧
      Integrable (complexEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
        (ArchimedeanLocal.dualFunction (r + 1) V) (complexFourierTransform a Φ) s) D.measure) ∧
  (∀ (ds es : List ComplexCharacterData), ds.length = r + 2 → es.length = r + 1 →
    ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r) (W : G → ℂ) (V : H → ℂ),
    W ∈ complexWhittakerModel (r + 1) ds a → V ∈ complexWhittakerModel r es (-a) →
    HasAdjacentJacquetConvergence a D W V)

theorem complexLocalJacquetEndpointConvergence :
    ComplexLocalJacquetEndpointConvergenceStatement (r := r) :=
  ⟨fun _ _ => complexLocalEqualEndpointConvergence,
    fun _ _ => complexLocalAdjacentEndpointConvergence⟩

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
