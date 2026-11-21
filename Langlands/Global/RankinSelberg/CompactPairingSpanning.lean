import Langlands.Global.RankinSelberg.ComplexLocalCompactWeight
import Langlands.Representation.Archimedean.FiniteTranslationSpan
import Langlands.Representation.Archimedean.RealInductionStagesFamily

/-! # Spanning by compact pairings on a fixed finite orbit -/

noncomputable section

open MeasureTheory
open Langlands.Archimedean.FiniteTranslationSpan (rightSpan)
open Langlands.Whittaker (rightTranslation)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

universe u

section Pairing

variable {K : Type u} [MeasurableSpace K]

private def pairing (μ : Measure K) (U : Submodule ℂ (K → ℂ)) (g : K → ℂ)
    (hint : ∀ w : U, Integrable (fun k => w.val k * g k) μ) : Module.Dual ℂ U where
  toFun w := ∫ k, w.val k * g k ∂μ
  map_add' w v := by
    simp only [Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (hint w) (hint v)
  map_smul' c w := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc,
      integral_const_mul, RingHom.id_apply]

end Pairing

/-- If continuous compact pairings distinguish a compact-finite profile from the
annihilator of a translation-stable family, the profile belongs to its algebraic span.
Only integrability against continuous weights is required for the family. -/
def CompactPairingSpanningStatement : Prop :=
  ∀ (K : Type u) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
    (f : K → ℂ) (S : Set (K → ℂ)),
    Continuous f → FiniteDimensional ℂ (rightSpan f) →
    (∀ g ∈ S, FiniteDimensional ℂ (rightSpan g) ∧ rightSpan g ≤ Submodule.span ℂ S) →
    (∀ g ∈ S, ∀ w : K → ℂ, Continuous w → Integrable (fun k => w k * g k) μ) →
    (∀ w : K → ℂ, Continuous w →
      (∀ g ∈ S, (∫ k, w k * g k ∂μ) = 0) → (∫ k, w k * f k ∂μ) = 0) →
    f ∈ Submodule.span ℂ S

theorem compactPairingSpanning : CompactPairingSpanningStatement.{u} := by
  intro K _ _ _ _ _ _ μ _ f S hf hfin hS hInt hDetect
  obtain ⟨κ, hκ, hκfin, hκf⟩ :=
    exists_compactWeight_of_finite_orbit μ (fun k : K => rightTranslation ℂ K k f)
      (fun x => hf.comp (continuous_const.mul continuous_id)) hfin <| by
      intro h x
      refine ⟨1, x * h⁻¹, fun k => ?_⟩
      change f (x * (h⁻¹ * k)) = 1 * f (x * h⁻¹ * k)
      rw [one_mul, mul_assoc]
  let U := Submodule.span ℂ (Set.range fun x : K => fun k => κ (x⁻¹ * k))
  let : FiniteDimensional ℂ U := hκfin
  let shift (x : K) : U := ⟨fun k => κ (x⁻¹ * k), Submodule.subset_span ⟨x, rfl⟩⟩
  have hU (w : U) : Continuous w.val := by
    refine Submodule.span_induction (p := fun v _ => Continuous v) ?_ continuous_const ?_ ?_ w.2
    · rintro _ ⟨x, rfl⟩
      exact hκ.comp (continuous_const.mul continuous_id)
    · intro _ _ _ _ hv₁ hv₂
      exact hv₁.add hv₂
    · intro _ _ _ hv
      exact continuous_const.smul hv
  let R : Module.Dual ℂ U →ₗ[ℂ] (K → ℂ) :=
    LinearMap.pi (fun x => Module.Dual.eval ℂ U (shift x))
  let F := pairing μ U f fun w =>
    ((hU w).mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let P (g : {g : K → ℂ // g ∈ S}) := pairing μ U g.val fun w => hInt g.val g.2 w.val (hU w)
  let A := Submodule.span ℂ (Set.range P)
  have hFA : F ∈ A := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := A), Submodule.mem_dualAnnihilator]
    intro w hw
    change (∫ k, w.val k * f k ∂μ) = 0
    apply hDetect w.val (hU w)
    intro g hg
    exact (Submodule.mem_dualCoannihilator w).mp hw (P ⟨g, hg⟩)
      (Submodule.subset_span ⟨⟨g, hg⟩, rfl⟩)
  have hshift (g : K → ℂ) (x : K) :
      (∫ k, κ (x⁻¹ * k) * g k ∂μ) = ∫ k, κ k * g (x * k) ∂μ := by
    simpa only [inv_mul_cancel_left] using
      (integral_mul_left_eq_self (fun k => κ (x⁻¹ * k) * g k) x).symm
  have hRF : R F = f := by
    funext x
    change (∫ k, κ (x⁻¹ * k) * f k ∂μ) = f x
    rw [hshift]
    have h := hκf x
    change (∫ k, κ k * f (x * k) ∂μ) = f (x * 1) at h
    simpa only [mul_one] using h
  have hRA : A ≤ (Submodule.span ℂ S).comap R := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    have : FiniteDimensional ℂ (rightSpan g) := (hS g hg).1
    change (fun x => ∫ k, κ (x⁻¹ * k) * g k ∂μ) ∈ Submodule.span ℂ S
    simp_rw [hshift]
    apply (hS g hg).2
    apply Langlands.Archimedean.InductionStages.integral_mem μ (rightSpan g)
    · intro k
      exact (rightSpan g).smul_mem (κ k) (Submodule.subset_span ⟨k, rfl⟩)
    · intro x
      have hI := hInt g hg (fun k => κ (x⁻¹ * k))
        (hκ.comp (continuous_const.mul continuous_id))
      have hT := ((measurePreserving_mul_left μ x).integrable_comp hI.aestronglyMeasurable).mpr hI
      refine hT.congr (ae_of_all _ fun k => ?_)
      change κ (x⁻¹ * (x * k)) * g (x * k) = κ k * g (x * k)
      rw [inv_mul_cancel_left]
  exact hRF ▸ hRA hFA

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
