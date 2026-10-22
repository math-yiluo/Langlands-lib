import Langlands.Representation.Hecke.TestFunction
import Langlands.Representation.Hecke.ActionIntegrand
import Langlands.HarmonicAnalysis.AlgebraicIntegral

/-! The actual finite-sum integral action on an algebraic smooth representation. -/

noncomputable section

namespace Langlands.Hecke

open HarmonicAnalysis MeasureTheory

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [OpensMeasurableSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Integration of the actual action integrand, bilinear in test function and
vector. There is no topology on the representation carrier. -/
def integratedAction (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) :
    SchwartzBruhat G →ₗ[ℂ] Module.End ℂ V where
  toFun f :=
    { toFun := fun v => AlgebraicIntegral.integral μ (actionIntegrand ρ hρ f v)
      map_add' := by
        intro v w
        change AlgebraicIntegral.integral μ (actionIntegrandLinear ρ hρ f (v + w)) = _
        rw [map_add]
        exact AlgebraicIntegral.integral_add _ _
          (actionIntegrand_finMeasSupp μ ρ hρ f v)
          (actionIntegrand_finMeasSupp μ ρ hρ f w)
      map_smul' := by
        intro c v
        change AlgebraicIntegral.integral μ (actionIntegrandLinear ρ hρ f (c • v)) = _
        rw [map_smul]
        exact AlgebraicIntegral.integral_smul c _
          (actionIntegrand_finMeasSupp μ ρ hρ f v) }
  map_add' := by
    intro f g
    ext v
    change AlgebraicIntegral.integral μ (actionIntegrandLinear ρ hρ (f + g) v) = _
    rw [map_add, LinearMap.add_apply]
    exact AlgebraicIntegral.integral_add _ _
      (actionIntegrand_finMeasSupp μ ρ hρ f v)
      (actionIntegrand_finMeasSupp μ ρ hρ g v)
  map_smul' := by
    intro c f
    ext v
    change AlgebraicIntegral.integral μ (actionIntegrandLinear ρ hρ (c • f) v) = _
    rw [map_smul, LinearMap.smul_apply]
    exact AlgebraicIntegral.integral_smul c _
      (actionIntegrand_finMeasSupp μ ρ hρ f v)

@[simp]
theorem integratedAction_apply (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (f : SchwartzBruhat G) (v : V) :
    integratedAction μ ρ hρ f v =
      AlgebraicIntegral.integral μ (actionIntegrand ρ hρ f v) := rfl

/-- Every finite measurable indicator presentation of the actual integrand gives
the same action. This includes support cutoffs, coset decompositions and their
refinements whenever they present the pointwise weighted orbit map. -/
theorem integratedAction_eq_sum_of_presentation
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (f : SchwartzBruhat G) (v : V) {I : Type*} (t : Finset I)
    (s : I → Set G) (w : I → V) (hs : ∀ i ∈ t, MeasurableSet (s i))
    (hfinite : ∀ i ∈ t, w i ≠ 0 → μ (s i) < ⊤)
    (hpres : ∀ x, f x • ρ x v = ∑ i ∈ t, (s i).indicator (fun _ => w i) x) :
    integratedAction μ ρ hρ f v = ∑ i ∈ t, ((μ (s i)).toReal : ℂ) • w i :=
  AlgebraicIntegral.integral_eq_of_indicator_presentation t s w hs hfinite
    (actionIntegrand ρ hρ f v) hpres

/-- Every algebraic linear functional computes the action by the ordinary scalar
Bochner integral. No continuity of the functional is assumed or needed. -/
theorem integratedAction_dual (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (f : SchwartzBruhat G) (v : V) (L : V →ₗ[ℂ] ℂ) :
    L (integratedAction μ ρ hρ f v) = ∫ g, f g * L (ρ g v) ∂μ := by
  rw [integratedAction_apply, ← AlgebraicIntegral.integral_linearMap _
    (actionIntegrand_finMeasSupp μ ρ hρ f v) L]
  rw [AlgebraicIntegral.integral_eq_bochner _
    ((actionIntegrand_finMeasSupp μ ρ hρ f v).map L.map_zero)]
  congr 1
  funext g
  simp

/-- Actual representation intertwiners commute with the integrated action. -/
theorem integratedAction_intertwiner (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (T : ρ.IntertwiningMap σ)
    (f : SchwartzBruhat G) (v : V) :
    T (integratedAction μ ρ hρ f v) =
      integratedAction μ σ hσ f (T v) := by
  change T.toLinearMap (AlgebraicIntegral.integral μ (actionIntegrand ρ hρ f v)) =
    AlgebraicIntegral.integral μ (actionIntegrand σ hσ f (T v))
  rw [← AlgebraicIntegral.integral_linearMap _
      (actionIntegrand_finMeasSupp μ ρ hρ f v) T.toLinearMap]
  congr 1
  exact actionIntegrand_intertwiner hρ hσ T f v

end Langlands.Hecke
