import Langlands.Representation.Hecke.IntegratedAction
import Langlands.HarmonicAnalysis.SchwartzBruhatProduct
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Finite sampling of the actual Hecke action on vectors fixed by an open subgroup. -/

noncomputable section

namespace Langlands.Hecke

open HarmonicAnalysis MeasureTheory
open scoped Topology

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A finite list of group elements and complex weights. -/
structure FiniteActionSamples (G : Type uG) where
  size : ℕ
  points : Fin size → G
  coefficients : Fin size → ℂ

private abbrev RightInvariantFunctions (K : OpenSubgroup G) :=
  {a : G → ℂ // ∀ (k : K) g, a (g * (k : G)) = a g}

private def rightInvariantExpansion (K : OpenSubgroup G) (f : SchwartzBruhat G)
    (hf : ∀ (k : K) g, f (g * (k : G)) = f g) :
    FiniteSchwartzExpansion (fun g (a : RightInvariantFunctions K) => f g * a.val g) := by
  apply finiteSchwartzExpansion
  · apply (IsLocallyConstant.iff_exists_open _).mpr
    intro g
    refine ⟨(fun x => g⁻¹ * x) ⁻¹' (K : Set G),
      K.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · simp
    · intro x hx
      funext a
      have hf' := hf ⟨g⁻¹ * x, hx⟩ g
      have ha' := a.property ⟨g⁻¹ * x, hx⟩ g
      simpa only [mul_inv_cancel_left] using congrArg₂ (· * ·) hf' ha'
  · exact (show HasCompactSupport (fun g => f g) from f.hasCompactSupport).smul_right

variable [MeasurableSpace G] [OpensMeasurableSpace G]

/-- Finite sampling data chosen from the test function and open subgroup alone.
No representation, vector, or representation-carrier universe enters the choice. -/
def fixedLevelActionSamples (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (K : OpenSubgroup G) (f : SchwartzBruhat G)
    (hf : ∀ (k : K) g, f (g * (k : G)) = f g) : FiniteActionSamples G :=
  let E := rightInvariantExpansion K f hf
  { size := E.size
    points := E.samples
    coefficients := fun i => (∫ g, E.functions i g ∂μ) * f (E.samples i) }

/-- The chosen data integrate every right-invariant scalar function after
weighting it by the test function. The scalar function needs no regularity
assumption beyond this subgroup invariance. -/
theorem fixedLevelActionSamples_integral
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (K : OpenSubgroup G) (f : SchwartzBruhat G)
    (hf : ∀ (k : K) g, f (g * (k : G)) = f g)
    (a : G → ℂ) (ha : ∀ (k : K) g, a (g * (k : G)) = a g) :
    (∫ g, f g * a g ∂μ) =
      ∑ i, (fixedLevelActionSamples μ K f hf).coefficients i *
        a ((fixedLevelActionSamples μ K f hf).points i) := by
  let E := rightInvariantExpansion K f hf
  have hE (g : G) : f g * a g =
      ∑ i, E.functions i g * (f (E.samples i) * a (E.samples i)) :=
    E.expansion ⟨a, ha⟩ g
  change (∫ g, f g * a g ∂μ) =
    ∑ i, ((∫ g, E.functions i g ∂μ) * f (E.samples i)) * a (E.samples i)
  rw [show (fun g => f g * a g) =
      (fun g => ∑ i, E.functions i g * (f (E.samples i) * a (E.samples i))) from
    funext hE]
  rw [integral_finsetSum _ (fun i _ =>
    ((E.functions i).integrable μ).mul_const (f (E.samples i) * a (E.samples i)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_mul_const, mul_assoc]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- On every vector fixed by the subgroup, the actual integrated action is the
same finite weighted sum of genuine group actions. The data work at every
representation-carrier universe, without a topology or dimension bound on it. -/
theorem fixedLevelActionSamples_action
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (K : OpenSubgroup G) (f : SchwartzBruhat G)
    (hf : ∀ (k : K) g, f (g * (k : G)) = f g)
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (v : V) (hv : v ∈ fixedVectors ρ K.toSubgroup) :
    integratedAction μ ρ hρ f v =
      ∑ i, (fixedLevelActionSamples μ K f hf).coefficients i •
        ρ ((fixedLevelActionSamples μ K f hf).points i) v := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro L
  rw [map_sub, sub_eq_zero, integratedAction_dual, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply fixedLevelActionSamples_integral μ K f hf (fun g => L (ρ g v))
  intro k g
  have hk : ρ (k : G) v = v := hv k
  rw [map_mul, Module.End.mul_apply, hk]

end Langlands.Hecke
