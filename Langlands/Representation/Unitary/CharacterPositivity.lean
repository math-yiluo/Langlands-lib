import Langlands.Representation.Hecke.UnimodularStar
import Langlands.Representation.Unitary.HermitianDual
import Langlands.Representation.Character.Basic
import Mathlib.Analysis.InnerProductSpace.Positive

/-! # Positive type of actual unitary distribution characters -/

noncomputable section

open scoped ComplexConjugate ComplexOrder Topology

namespace Langlands

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis Filter

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
  {ρ : Representation ℂ G V}

namespace InvariantPositiveForm

/-- Conjugate inversion gives the adjoint of the actual algebraic integral. -/
theorem integratedAction_adjoint [IsInvInvariant μ]
    (b : InvariantPositiveForm ρ) (hρ : IsSmooth ρ)
    (f : SchwartzBruhat G) (v w : V) :
    b.inner (Hecke.integratedAction μ ρ hρ (Hecke.TestFunction.adjoint f) v) w =
      b.inner v (Hecke.integratedAction μ ρ hρ f w) := by
  calc
    _ = conj (b.rightFunctional w
        (Hecke.integratedAction μ ρ hρ (Hecke.TestFunction.adjoint f) v)) :=
      (b.conj_inner_symm _ _).symm
    _ = conj (∫ g, conj (f g⁻¹) * b.inner w (ρ g v) ∂μ) := by
      rw [Hecke.integratedAction_dual]
      rfl
    _ = ∫ g, f g⁻¹ * b.inner (ρ g v) w ∂μ := by
      rw [← integral_conj]
      congr 1
      funext g
      simp only [map_mul, Complex.conj_conj, b.conj_inner_symm]
    _ = ∫ g, f g⁻¹ * b.inner v (ρ g⁻¹ w) ∂μ := by
      congr 1
      funext g
      rw [← b.invariant g v (ρ g⁻¹ w), Representation.self_inv_apply]
    _ = ∫ g, f g * b.inner v (ρ g w) ∂μ :=
      integral_inv_eq_self (fun g => f g * b.inner v (ρ g w)) μ
    _ = _ := (Hecke.integratedAction_dual μ ρ hρ f w (b.rightFunctional v)).symm

end InvariantPositiveForm

namespace Character

/-- Positive type means nonnegative values on every Hecke square `f† * f`.
This differs from positivity of a measure on pointwise nonnegative functions. -/
def IsPositiveType (D : Distribution G) : Prop :=
  ∀ f : SchwartzBruhat G,
    0 ≤ D (Hecke.TestFunction.convolution μ (Hecke.TestFunction.adjoint f) f)

/-- Positive type is preserved by pointwise convergence of distributions. -/
theorem IsPositiveType.of_tendsto {D : ℕ → Distribution G} {D₀ : Distribution G}
    (hD : ∀ n, IsPositiveType μ (D n))
    (hlim : ∀ f, Tendsto (fun n => D n f) atTop (𝓝 (D₀ f))) :
    IsPositiveType μ D₀ := by
  intro f
  exact ge_of_tendsto (hlim _) (Eventually.of_forall fun n => hD n f)

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [IsMulLeftInvariant μ] [IsInvInvariant μ]

/-- The genuine finite-rank character of an admissible unitarizable
representation is of positive type. -/
theorem distribution_isPositiveType (hρ : IsAdmissible ρ)
    (hu : IsUnitarizable ρ) : IsPositiveType μ (distribution μ ρ hρ) := by
  classical
  obtain ⟨b⟩ := hu
  intro f
  obtain ⟨K, _, _, hf⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G {f} ⊤
  have hfK := hf f (Finset.mem_singleton_self f)
  have hsK := Hecke.TestFunction.convolution_mem_biInvariant μ
    (Hecke.TestFunction.adjoint_mem_biInvariant hfK) hfK
  let U := fixedVectors ρ K.toSubgroup
  let : FiniteDimensional ℂ U := hρ.2 K
  let c : InnerProductSpace.Core ℂ U :=
    { inner := fun v w => b.inner v.val w.val
      conj_inner_symm := fun v w => b.conj_inner_symm v.val w.val
      re_inner_nonneg := fun v => b.re_inner_nonneg v.val
      add_left := fun v w x => b.add_left v.val w.val x.val
      smul_left := fun v w a => b.smul_left v.val w.val a
      definite := fun v hv => Subtype.ext (b.definite v.val hv) }
  let : NormedAddCommGroup U :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ U _ _ _ c
  let : InnerProductSpace ℂ U := InnerProductSpace.ofCore c.toCore
  let S : Module.End ℂ U :=
    (Hecke.integratedActionToFixed μ ρ hρ.1 hsK).comp U.subtype
  have hS : S.IsPositive := by
    apply (LinearMap.isPositive_iff_complex S).2
    intro v
    have he : inner ℂ (S v) v =
        b.inner (Hecke.integratedAction μ ρ hρ.1 f v.val)
          (Hecke.integratedAction μ ρ hρ.1 f v.val) := by
      change b.inner
        (Hecke.integratedAction μ ρ hρ.1
          (Hecke.TestFunction.convolution μ (Hecke.TestFunction.adjoint f) f) v.val)
        v.val = _
      rw [Hecke.integratedAction_convolution, InvariantPositiveForm.integratedAction_adjoint μ b hρ.1]
    rw [he]
    let := b.toInnerProductCore
    exact ⟨InnerProductSpace.Core.inner_self_ofReal_re _, b.re_inner_nonneg _⟩
  rw [distribution_eq_fixedVectors μ ρ hρ K hsK]
  exact hS.trace_nonneg

end Character
end Langlands
