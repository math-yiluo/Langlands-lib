import Langlands.HarmonicAnalysis.SmoothWeakIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! # Fubini and measurable coordinates for smooth weak integration -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.SmoothWeakIntegral

universe uX uY uZ uG uV

variable {X : Type uX} {Y : Type uY} {Z : Type uZ}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (μ : Measure X) (ν : Measure Y)

/-- Absolute integrability on the product is tested by every actual smooth
functional. It does not assert existence of a representing vector. -/
def ScalarProductIntegrable (f : X × Y → V) : Prop :=
  ∀ ℓ : SmoothDual ρ, MeasureTheory.Integrable (fun p => ℓ.val (f p)) (μ.prod ν)

variable {ρ μ ν} {f : X × Y → V} {j : Y → V} {v : V}

section Product

variable [SFinite μ] [SFinite ν]

/-- Genuine product absolute convergence is equivalent to almost-everywhere
fiber convergence and integrability of the fiber absolute integrals, provided
the joint scalar tests are almost-everywhere strongly measurable. -/
theorem scalarProductIntegrable_iff
    (hm : ∀ ℓ : SmoothDual ρ,
      AEStronglyMeasurable (fun p => ℓ.val (f p)) (μ.prod ν)) :
    ScalarProductIntegrable ρ μ ν f ↔
      ∀ ℓ : SmoothDual ρ,
        (∀ᵐ y ∂ν, MeasureTheory.Integrable (fun x => ℓ.val (f (x, y))) μ) ∧
          MeasureTheory.Integrable (fun y => ∫ x, ‖ℓ.val (f (x, y))‖ ∂μ) ν :=
  forall_congr' fun ℓ => integrable_prod_iff' (hm ℓ)

/-- If the fiber weak integrals are represented in the original carrier,
scalar Fubini identifies the product weak integral with the outer weak
integral. Joint absolute convergence is an explicit hypothesis. -/
theorem hasIntegral_prod_iff
    (hf : ScalarProductIntegrable ρ μ ν f)
    (hj : ∀ᵐ y ∂ν, HasIntegral ρ μ (fun x => f (x, y)) (j y)) :
    HasIntegral ρ (μ.prod ν) f v ↔ HasIntegral ρ ν j v := by
  have he (ℓ : SmoothDual ρ) :
      (fun y => ∫ x, ℓ.val (f (x, y)) ∂μ) =ᵐ[ν] fun y => ℓ.val (j y) := by
    filter_upwards [hj] with y hy
    exact (hy ℓ).2
  constructor
  · intro h ℓ
    refine ⟨(hf ℓ).integral_prod_right.congr (he ℓ), ?_⟩
    rw [← integral_congr_ae (he ℓ), ← integral_prod_symm _ (hf ℓ)]
    exact (h ℓ).2
  · intro h ℓ
    refine ⟨hf ℓ, ?_⟩
    rw [integral_prod_symm _ (hf ℓ), integral_congr_ae (he ℓ)]
    exact (h ℓ).2

/-- Fiberwise representability and an outer representing vector yield a
product representing vector when all scalar product tests converge absolutely. -/
theorem HasIntegral.prod
    (hj : HasIntegral ρ ν j v)
    (hf : ScalarProductIntegrable ρ μ ν f)
    (hinner : ∀ᵐ y ∂ν, HasIntegral ρ μ (fun x => f (x, y)) (j y)) :
    HasIntegral ρ (μ.prod ν) f v :=
  (hasIntegral_prod_iff hf hinner).mpr hj

/-- Given original-carrier representatives of the fibers and genuine scalar
product convergence, existence of a product representative is equivalent to
existence of an outer representative. -/
theorem integrable_prod_iff
    (hf : ScalarProductIntegrable ρ μ ν f)
    (hj : ∀ᵐ y ∂ν, HasIntegral ρ μ (fun x => f (x, y)) (j y)) :
    Integrable ρ (μ.prod ν) f ↔ Integrable ρ ν j :=
  exists_congr fun _ => hasIntegral_prod_iff hf hj

/-- The existing chosen linear integrals obey Fubini on their actual
representability domains. No completed or bidual carrier is introduced. -/
theorem integralLinear_prod [IsTopologicalGroup G]
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K) (hρ : IsSmooth ρ)
    (F : integrableSubmodule ρ (μ.prod ν)) (J : integrableSubmodule ρ ν)
    (hinner : ∀ᵐ y ∂ν, HasIntegral ρ μ (fun x => F.val (x, y)) (J.val y)) :
    integralLinear hcofinal hρ F = integralLinear hcofinal hρ J :=
  integralLinear_eq hcofinal hρ F
    ((integralLinear_spec hcofinal hρ J).prod
      (fun ℓ => ((integralLinear_spec hcofinal hρ F) ℓ).1) hinner)

end Product

/-- A measurable equivalence transports all original scalar tests and their
representing vector, with precisely the pushed-forward measure. -/
theorem hasIntegral_map_equiv_iff (e : X ≃ᵐ Z) (μ : Measure X)
    (f : Z → V) (v : V) :
    HasIntegral ρ (Measure.map e μ) f v ↔
      HasIntegral ρ μ (fun x => f (e x)) v := by
  apply forall_congr'
  intro ℓ
  exact and_congr (integrable_map_equiv e (fun z => ℓ.val (f z)))
    (by rw [integral_map_equiv e (fun z => ℓ.val (f z))])

/-- Prescribed source and target measures are interchangeable along a
measure-preserving measurable equivalence. This asserts no normalization
for an independently supplied target measure. -/
theorem hasIntegral_measurePreserving_equiv_iff (e : X ≃ᵐ Z)
    {μ : Measure X} {τ : Measure Z}
    (he : MeasurePreserving e μ τ) (f : Z → V) (v : V) :
    HasIntegral ρ τ f v ↔ HasIntegral ρ μ (fun x => f (e x)) v := by
  rw [← he.map_eq]
  exact hasIntegral_map_equiv_iff e μ f v

end Langlands.HarmonicAnalysis.SmoothWeakIntegral
