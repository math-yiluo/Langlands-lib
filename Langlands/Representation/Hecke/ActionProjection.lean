import Langlands.Representation.Hecke.IntegratedConvolution
import Langlands.Representation.Hecke.NormalizedIndicator

/-! Normalized Hecke indicators act as actual fixed-vector projections. -/

noncomputable section

namespace Langlands.Hecke

open HarmonicAnalysis MeasureTheory MeasureTheory.Measure

universe uG uV uW

section Projection

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

variable (μ : Measure G) [μ.IsHaarMeasure]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- The actual normalized indicator fixes each K-fixed vector. -/
theorem heckeAction_normalizedIndicator_of_fixed {v : V}
    (hv : v ∈ fixedVectors ρ K.toSubgroup) :
    heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ K hK) v = v := by
  change integratedAction μ ρ hρ
    (((μ.real (K : Set G) : ℂ)⁻¹) • TestFunction.subgroupIndicator K hK) v = v
  rw [map_smul, LinearMap.smul_apply,
    integratedAction_subgroupIndicator_of_fixed μ ρ hρ K hK hv]
  change (μ.real (K : Set G) : ℂ)⁻¹ • ((μ.real (K : Set G) : ℂ) • v) = v
  rw [smul_smul, inv_mul_cancel₀ (HeckeAlgebra.compactOpen_complex_mass_ne_zero μ K hK),
    one_smul]

/-- The image of the normalized indicator consists of K-fixed vectors. -/
theorem heckeAction_normalizedIndicator_mem (v : V) :
    heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ K hK) v ∈
      fixedVectors ρ K.toSubgroup :=
  integratedAction_mem_fixedVectors μ ρ hρ
    (HeckeAlgebra.normalizedIndicator_mem_biInvariant μ K hK) v

/-- The indicator action, with its codomain restricted to the existing fixed vectors. -/
def fixedProjection : V →ₗ[ℂ] fixedVectors ρ K.toSubgroup :=
  (heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ K hK)).codRestrict
    (fixedVectors ρ K.toSubgroup) (heckeAction_normalizedIndicator_mem μ ρ hρ K hK)

@[simp]
theorem fixedProjection_apply (v : V) :
    (fixedProjection μ ρ hρ K hK v : V) =
      heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ K hK) v := rfl

@[simp]
theorem fixedProjection_fixed (v : fixedVectors ρ K.toSubgroup) :
    fixedProjection μ ρ hρ K hK (v : V) = v :=
  Subtype.ext (heckeAction_normalizedIndicator_of_fixed μ ρ hρ K hK v.property)

/-- The range of the actual normalized Hecke operator is exactly the fixed subspace. -/
theorem heckeAction_normalizedIndicator_range :
    LinearMap.range (heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ K hK)) =
      fixedVectors ρ K.toSubgroup := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact heckeAction_normalizedIndicator_mem μ ρ hρ K hK v
  · intro v hv
    exact ⟨v, heckeAction_normalizedIndicator_of_fixed μ ρ hρ K hK hv⟩

/-- Idempotence follows from actual convolution multiplicativity. -/
theorem heckeAction_normalizedIndicator_idempotent :
    ∀ v : V, heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ K hK)
      (heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ K hK) v) =
      heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ K hK) v := by
  intro v
  have h := congrArg (fun f : HeckeAlgebra μ => heckeAction μ ρ hρ f v)
    (HeckeAlgebra.normalizedIndicator_idempotent μ K hK)
  simpa only [map_mul, Module.End.mul_apply] using h

/-- The existing fixed-vector map intertwines the normalized projections. -/
theorem fixedProjection_intertwiner {σ : Representation ℂ G W} (hσ : IsSmooth σ)
    (T : ρ.IntertwiningMap σ) (v : V) :
    fixedVectorsMap T K.toSubgroup (fixedProjection μ ρ hρ K hK v) =
      fixedProjection μ σ hσ K hK (T v) := by
  apply Subtype.ext
  exact integratedAction_intertwiner μ hρ hσ T
    (HeckeAlgebra.toTestFunction μ (HeckeAlgebra.normalizedIndicator μ K hK)) v

/-- A smaller compact open subgroup fixes the output of the larger projection. -/
theorem fixedProjection_refinement_left (J : OpenSubgroup G)
    (hJ : IsCompact (J : Set G)) (hJK : J ≤ K) (v : V) :
    heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ J hJ)
      (heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ K hK) v) =
      heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ K hK) v := by
  have h := congrArg (fun f : HeckeAlgebra μ => heckeAction μ ρ hρ f v)
    (HeckeAlgebra.normalizedIndicator_mul_of_le μ K hK J hJ hJK)
  simpa only [map_mul, Module.End.mul_apply] using h

/-- Averaging over the larger subgroup absorbs averaging over a smaller subgroup. -/
theorem fixedProjection_refinement_right (J : OpenSubgroup G)
    (hJ : IsCompact (J : Set G)) (hJK : J ≤ K) (v : V) :
    heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ K hK)
      (heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ J hJ) v) =
      heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ K hK) v := by
  have h := congrArg (fun f : HeckeAlgebra μ => heckeAction μ ρ hρ f v)
    (HeckeAlgebra.normalizedIndicator_mul_of_ge μ K hK J hJ hJK)
  simpa only [map_mul, Module.End.mul_apply] using h

end Projection

end Langlands.Hecke
