import Langlands.Group.Unitary.Basic
import Langlands.HarmonicAnalysis.Bicharacter.SelfDual
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# The topology of a quadratic extension of a nonarchimedean local field

Let `F` be a nonarchimedean local field and `E = F(δ)` a quadratic extension with conjugation `c`
(`hE : IsQuadraticInvolution c δ`), with the module topology over `F`. Then `E` is a Hausdorff
topological field (`isTopologicalRing`, `continuousInv₀`, `t2Space`), and the conjugation, the
trace and the norm are continuous (`continuous_conj`, `continuous_trace`, `continuous_norm`). The
inverse is `z⁻¹ = N(z)⁻¹ c(z)`, which gives its continuity away from `0`. The matrix spaces
`M_{α×ν}(E)` carry the module topology over `F` (`HarmonicAnalysis.isModuleTopology_matrix`);
with the
finite-dimensionality of `E` (`IsQuadraticInvolution.finite`) the results of
`Langlands.HarmonicAnalysis.Bicharacter.SelfDual` (compact open exhaustion, Hausdorff, locally
compact, second countable) apply to them.
-/

namespace Langlands.IsQuadraticInvolution

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type*} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
  {c : E →ₐ[F] E} {δ : E}

/-- A quadratic extension with the module topology is a topological ring. -/
theorem isTopologicalRing (hE : IsQuadraticInvolution c δ) : IsTopologicalRing E :=
  have := hE.finite
  IsModuleTopology.isTopologicalRing F E

/-- The conjugation is continuous. -/
theorem continuous_conj (hE : IsQuadraticInvolution c δ) : Continuous c :=
  have := hE.finite
  have := hE.isTopologicalRing
  IsModuleTopology.continuous_of_linearMap c.toLinearMap

/-- The trace is continuous. -/
theorem continuous_trace (hE : IsQuadraticInvolution c δ) : Continuous (Algebra.trace F E) :=
  have := hE.finite
  have := hE.isTopologicalRing
  IsModuleTopology.continuous_of_linearMap (Algebra.trace F E)

/-- A quadratic extension of a nonarchimedean local field is Hausdorff. -/
theorem t2Space (hE : IsQuadraticInvolution c δ) : T2Space E :=
  have := hE.finite
  HarmonicAnalysis.t2Space_of_finiteDimensional F E

variable [NeZero (2 : F)]

/-- The norm is continuous: `N z = ½ tr (z c(z))`. -/
theorem continuous_norm (hE : IsQuadraticInvolution c δ) :
    Continuous (Algebra.norm F : E → F) := by
  obtain ⟨b, -, -⟩ := hE.exists_basis
  have : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have : IsTopologicalRing E := hE.isTopologicalRing
  have hN : ∀ z : E, Algebra.norm F z = (2 : F)⁻¹ * Algebra.trace F E (z * c z) := by
    intro z
    rw [← hE.algebraMap_norm z, Algebra.trace_algebraMap, Module.finrank_eq_card_basis b,
        Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have : (Algebra.norm F : E → F) = fun z => (2 : F)⁻¹ * Algebra.trace F E (z * c z) := funext hN
  rw [this]
  exact continuous_const.mul (hE.continuous_trace.comp (continuous_id.mul hE.continuous_conj))

/-- The inverse is continuous away from `0`: `z⁻¹ = N(z)⁻¹ c(z)`. -/
theorem continuousInv₀ (hE : IsQuadraticInvolution c δ) : ContinuousInv₀ E := by
  have := hE.finite
  have : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have : ContinuousSMul F E := IsModuleTopology.toContinuousSMul F E
  have hinv : ∀ z : E, z⁻¹ = (Algebra.norm F z)⁻¹ • c z := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · have hn : Algebra.norm F z ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hz
      symm
      apply eq_inv_of_mul_eq_one_left
      rw [Algebra.smul_def, mul_assoc, mul_comm (c z) z, ← hE.algebraMap_norm z, ← map_mul,
          inv_mul_cancel₀ hn, map_one]
  refine ⟨fun z hz => ?_⟩
  have : (Inv.inv : E → E) = fun z => (Algebra.norm F z)⁻¹ • c z := funext hinv
  rw [this]
  have hn : Algebra.norm F z ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hz
  exact ((continuousAt_inv₀ hn).comp hE.continuous_norm.continuousAt).smul
    hE.continuous_conj.continuousAt

end Langlands.IsQuadraticInvolution
