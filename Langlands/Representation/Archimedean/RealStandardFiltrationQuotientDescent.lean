import Langlands.Representation.Archimedean.RealStandardFiltration
import Mathlib.Algebra.Module.Projective

/-! # Replacing a filtration source by an exact quotient -/

noncomputable section

open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean
namespace RealStandardFiltration

open Langlands.LocalFactor.Archimedean

variable {n : ℕ} {R S V : List RealBlock}
  {N : Submodule ℂ (KF n V)}
  {T : KF n R →ₗ[ℂ] KF n V} {U : KF n R →ₗ[ℂ] KF n S}

/-- A linear section induces a map modulo `N` when the quotient kernel maps into `N`. -/
theorem modulo_quotient_section
    (hT : IsRealIntertwinerModulo n R V N T)
    (hU : IsRealIntertwinerModulo n R S ⊥ U)
    (s : KF n S →ₗ[ℂ] KF n R) (hs : U.comp s = LinearMap.id)
    (hker : (LinearMap.ker U).map T ≤ N) :
    IsRealIntertwinerModulo n S V N (T.comp s) := by
  have hsec : ∀ f, U (s f) = f := fun f => LinearMap.congr_fun hs f
  refine ⟨fun κ f => ?_, fun X f => ?_⟩
  · obtain ⟨hr, hv, ht⟩ := hT.1 κ (s f)
    obtain ⟨_, hsf, hu⟩ := hU.1 κ (s f)
    rw [Submodule.mem_bot, sub_eq_zero] at hu
    have hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (κ : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ) ∈ KF n S := by
      simpa only [hsec] using hsf
    have hu' : U ⟨_, hr⟩ = ⟨_, hf⟩ := by
      apply Subtype.ext
      simpa only [hsec] using
        congrArg (fun z : KF n S => (z : Langlands.GeneralLinear n ℝ → ℂ)) hu
    have hk : s ⟨_, hf⟩ - ⟨_, hr⟩ ∈ LinearMap.ker U := by
      rw [LinearMap.mem_ker, map_sub, hsec, hu', sub_self]
    have hm := hker (Submodule.mem_map_of_mem hk)
    refine ⟨hf, hv, ?_⟩
    change T (s ⟨_, hf⟩) - ⟨_, hv⟩ ∈ N
    have heq : T (s ⟨_, hf⟩) - (⟨_, hv⟩ : KF n V) =
        T (s ⟨_, hf⟩ - ⟨_, hr⟩) + (T ⟨_, hr⟩ - ⟨_, hv⟩) := by
      rw [map_sub]
      abel
    rw [heq]
    exact N.add_mem hm ht
  · obtain ⟨hr, hv, ht⟩ := hT.2 X (s f)
    obtain ⟨_, hsf, hu⟩ := hU.2 X (s f)
    rw [Submodule.mem_bot, sub_eq_zero] at hu
    have hf : rightDerivative (matrixModel ℝ n) X
        (f : Langlands.GeneralLinear n ℝ → ℂ) ∈ KF n S := by
      simpa only [hsec] using hsf
    have hu' : U ⟨_, hr⟩ = ⟨_, hf⟩ := by
      apply Subtype.ext
      simpa only [hsec] using
        congrArg (fun z : KF n S => (z : Langlands.GeneralLinear n ℝ → ℂ)) hu
    have hk : s ⟨_, hf⟩ - ⟨_, hr⟩ ∈ LinearMap.ker U := by
      rw [LinearMap.mem_ker, map_sub, hsec, hu', sub_self]
    have hm := hker (Submodule.mem_map_of_mem hk)
    refine ⟨hf, hv, ?_⟩
    change T (s ⟨_, hf⟩) - ⟨_, hv⟩ ∈ N
    have heq : T (s ⟨_, hf⟩) - (⟨_, hv⟩ : KF n V) =
        T (s ⟨_, hf⟩ - ⟨_, hr⟩) + (T ⟨_, hr⟩ - ⟨_, hv⟩) := by
      rw [map_sub]
      abel
    rw [heq]
    exact N.add_mem hm ht

/-- Replacing the source by its quotient preserves the span together with `N`. -/
theorem sup_range_quotient_section
    (s : KF n S →ₗ[ℂ] KF n R) (hs : U.comp s = LinearMap.id)
    (hker : (LinearMap.ker U).map T ≤ N) :
    N ⊔ LinearMap.range (T.comp s) = N ⊔ LinearMap.range T := by
  have hsec : ∀ f, U (s f) = f := fun f => LinearMap.congr_fun hs f
  apply le_antisymm
  · exact sup_le_sup_left (LinearMap.range_comp_le_range s T) N
  · refine sup_le le_sup_left ?_
    rintro _ ⟨f, rfl⟩
    have hk : f - s (U f) ∈ LinearMap.ker U := by
      rw [LinearMap.mem_ker, map_sub, hsec, sub_self]
    have hm := hker (Submodule.mem_map_of_mem hk)
    have heq : T f = T (f - s (U f)) + (T.comp s) (U f) := by
      rw [map_sub, LinearMap.comp_apply, sub_add_cancel]
    rw [heq]
    exact add_mem (Submodule.mem_sup_left hm) (Submodule.mem_sup_right ⟨U f, rfl⟩)

/-- Exact surjective quotients can replace a source modulo its kernel image. -/
theorem exists_quotient_descent
    (hT : IsRealIntertwinerModulo n R V N T)
    (hU : IsRealIntertwinerModulo n R S ⊥ U)
    (hsurj : Function.Surjective U) (hker : (LinearMap.ker U).map T ≤ N) :
    ∃ q : KF n S →ₗ[ℂ] KF n V,
      IsRealIntertwinerModulo n S V N q ∧
        N ⊔ LinearMap.range q = N ⊔ LinearMap.range T := by
  obtain ⟨s, hs⟩ := U.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  exact ⟨T.comp s, modulo_quotient_section hT hU s hs hker,
    sup_range_quotient_section s hs hker⟩

end RealStandardFiltration

open Langlands.LocalFactor.Archimedean RealStandardFiltration in
/-- An exact quotient replaces a source modulo the image of its kernel. -/
def RealStandardFiltrationQuotientDescentStatement : Prop :=
  ∀ (n : ℕ) (R S V : List RealBlock) (N : Submodule ℂ (KF n V))
    (T : KF n R →ₗ[ℂ] KF n V) (U : KF n R →ₗ[ℂ] KF n S),
    IsRealIntertwinerModulo n R V N T →
    IsRealIntertwinerModulo n R S ⊥ U →
    Function.Surjective U → (LinearMap.ker U).map T ≤ N →
    ∃ q : KF n S →ₗ[ℂ] KF n V,
      IsRealIntertwinerModulo n S V N q ∧
        N ⊔ LinearMap.range q = N ⊔ LinearMap.range T

theorem realStandardFiltrationQuotientDescent :
    RealStandardFiltrationQuotientDescentStatement :=
  fun _ _ _ _ _ _ _ hT hU hsurj hker =>
    RealStandardFiltration.exists_quotient_descent hT hU hsurj hker

end Langlands.Archimedean
