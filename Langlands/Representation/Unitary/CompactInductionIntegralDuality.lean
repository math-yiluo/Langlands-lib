import Langlands.Representation.Induction.CompactQuotientSmoothDuality
import Langlands.Representation.Smooth.Contragredient.Equivalence

/-! # Normalized compact induction and duality for a compact quotient -/

noncomputable section

open CategoryTheory MeasureTheory
open scoped NNReal

namespace Langlands.Induction

universe uG v w

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [LocallyCompactSpace G]

section Compact

variable (P : Subgroup G) [CompactSpace (LeftQuotient P)]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- When the quotient is compact, compact and smooth induction have the same
functions, with the same right-translation action. -/
def compactQuotientInductionEquiv (σ : Representation ℂ P V) :
    (compactInduced P σ).Equiv (smoothInduced P σ) :=
  Representation.Equiv.mk
    { toFun := Subtype.val
      invFun f := ⟨f, (isClosed_quotientSupport P σ f).isCompact⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    (fun _ => rfl)

/-- The integral-characterized duality for compact induction, transported
through the inclusion into smooth induction. -/
theorem exists_compactIntegralDualEquiv
    (hP : IsClosed (P : Set G)) (χ : P →* ℂˣ) (hχ : IsOpen (χ.ker : Set P))
    (δ : P → ℝ≥0) (hδ : ∀ q : P, (χ q : ℂ) * χ q = ((δ q : ℝ) : ℂ))
    (K : Subgroup G) [MeasurableSpace K] (μ : Measure K)
    (hpos : ∀ U : Set K, IsOpen U → (1 : K) ∈ U → 0 < μ U)
    (hscalar : ∀ φ : G → ℂ, IsLocallyConstant φ →
      (∀ (q : P) (x : G), φ ((q : G) * x) = ((δ q : ℝ) : ℂ) * φ x) →
      ∀ g : G, Integrable (fun k : K => φ ((k : G) * g)) μ ∧
        (∫ k : K, φ ((k : G) * g) ∂μ) = ∫ k : K, φ (k : G) ∂μ)
    (σ : Representation ℂ P V) (hσ : IsSmooth σ) :
    ∃ E : Representation.Equiv
        (smoothContragredient (compactInduced P (twist χ σ)))
        (compactInduced P (twist χ (smoothContragredient σ))),
      ∀ (ℓ : SmoothDual (compactInduced P (twist χ σ)))
        (f : CompactFunctions P (twist χ σ)),
        smoothDualPairing _ ℓ f =
          ∫ k : K, smoothDualPairing σ (eval P _ (E ℓ).val k)
            (eval P _ f.val k) ∂μ := by
  obtain ⟨F, hF⟩ := exists_integralDualEquiv_of_section P (MonoidHom.id P) χ δ K μ
    continuous_id hχ hδ hpos hscalar hP (MonoidHom.id P) continuous_id
    (fun _ => rfl) σ hσ
  let c := compactQuotientInductionEquiv P (twist χ σ)
  let d := compactQuotientInductionEquiv P (twist χ (smoothContragredient σ))
  let E := ((smoothContragredientEquiv c.symm).trans F).trans d.symm
  refine ⟨E, fun ℓ f => ?_⟩
  exact hF (smoothContragredientEquiv c.symm ℓ) (c f)

end Compact

end Langlands.Induction
