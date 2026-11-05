import Langlands.HarmonicAnalysis.SmoothWeakIntegral

/-! # Scalar integration as an algebraic functional -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.SmoothWeakIntegral

universe uX uG uV

variable {X : Type uX} [MeasurableSpace X]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (μ : Measure X) (f : X → V)

/-- Integrating every smooth scalar test defines an actual algebraic functional
on the smooth dual. Its integrability assumption ensures linearity. -/
def scalarIntegralFunctional
    (hf : ∀ ℓ : SmoothDual ρ, MeasureTheory.Integrable (fun x => ℓ.val (f x)) μ) :
    Module.Dual ℂ (SmoothDual ρ) where
  toFun ℓ := ∫ x, ℓ.val (f x) ∂μ
  map_add' ℓ ψ := by
    change (∫ x, ℓ.val (f x) + ψ.val (f x) ∂μ) = _
    exact integral_add (hf ℓ) (hf ψ)
  map_smul' c ℓ := by
    change (∫ x, c • ℓ.val (f x) ∂μ) = _
    exact integral_smul c _

@[simp] theorem scalarIntegralFunctional_apply
    (hf : ∀ ℓ : SmoothDual ρ, MeasureTheory.Integrable (fun x => ℓ.val (f x)) μ)
    (ℓ : SmoothDual ρ) :
    scalarIntegralFunctional ρ μ f hf ℓ = ∫ x, ℓ.val (f x) ∂μ := rfl

variable [IsTopologicalGroup G]

/-- Integral invariance under an open subgroup places the scalar-integral
functional in the actual smooth bidual. -/
def smoothScalarIntegralFunctional
    (hf : ∀ ℓ : SmoothDual ρ, MeasureTheory.Integrable (fun x => ℓ.val (f x)) μ)
    (K : OpenSubgroup G)
    (hK : ∀ (k : K) (ℓ : SmoothDual ρ),
      (∫ x, (smoothContragredient ρ (k : G) ℓ).val (f x) ∂μ) =
        ∫ x, ℓ.val (f x) ∂μ) :
    SmoothDual (smoothContragredient ρ) :=
  ⟨scalarIntegralFunctional ρ μ f hf, K, fun k => by
    apply LinearMap.ext
    intro ℓ
    change (∫ x, (smoothContragredient ρ (k : G)⁻¹ ℓ).val (f x) ∂μ) =
      ∫ x, ℓ.val (f x) ∂μ
    exact hK k⁻¹ ℓ⟩

/-- Admissible smooth biduality recovers a representing vector in the original
carrier, once the scalar integral is invariant under an open subgroup. -/
theorem integrable_of_scalar_integrable_of_invariant
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsAdmissible ρ)
    (hf : ∀ ℓ : SmoothDual ρ, MeasureTheory.Integrable (fun x => ℓ.val (f x)) μ)
    (K : OpenSubgroup G)
    (hK : ∀ (k : K) (ℓ : SmoothDual ρ),
      (∫ x, (smoothContragredient ρ (k : G) ℓ).val (f x) ∂μ) =
        ∫ x, ℓ.val (f x) ∂μ) :
    Integrable ρ μ f := by
  obtain ⟨v, hv⟩ := smoothBidual_surjective_of_compact_cofinal hcofinal ρ hρ
    (smoothScalarIntegralFunctional ρ μ f hf K hK)
  refine ⟨v, fun ℓ => ⟨hf ℓ, ?_⟩⟩
  have he := congrArg (fun ψ : SmoothDual (smoothContragredient ρ) => ψ.val ℓ) hv
  exact he.symm

end Langlands.HarmonicAnalysis.SmoothWeakIntegral
