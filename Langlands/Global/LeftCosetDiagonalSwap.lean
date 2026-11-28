import Langlands.Global.LeftCosetHaarMeasure
import Langlands.Global.AdelicConstantTermAverage

/-! # Exchanging the variables of a diagonally invariant double integral over `Γ \ H × H` -/

noncomputable section

universe u

open MeasureTheory Set

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace

section Basic

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (Γ : Subgroup H)

omit [TopologicalSpace H] [IsTopologicalGroup H] in
/-- A representative of the class of `x` differs from `x` by an element of `Γ`. -/
theorem exists_out_eq (x : H) : ∃ γ : Γ, (Quotient.out (mk Γ x) : H) = (γ : H) * x := by
  have h : mk Γ (Quotient.out (mk Γ x)) = mk Γ x := Quotient.out_eq _
  have h' := (mk_eq_mk_iff Γ _ _).mp h.symm
  exact ⟨⟨_, h'⟩, by simp⟩

/-- A continuous function on `H × H` invariant under `Γ` in the first variable, read at
representatives of `Γ \ H`, is continuous on `Γ \ H × H`. -/
theorem continuous_out_prod {E : Type*} [TopologicalSpace E] (f : H × H → E) (hf : Continuous f)
    (hinv : ∀ (γ : Γ) (x z : H), f ((γ : H) * x, z) = f (x, z)) :
    Continuous fun p : LeftCosetSpace Γ × H => f (Quotient.out p.1, p.2) := by
  rw [← ((isOpenQuotientMap_mk Γ).prodMap IsOpenQuotientMap.id).continuous_comp_iff]
  have heq : ((fun p : LeftCosetSpace Γ × H => f (Quotient.out p.1, p.2)) ∘
      Prod.map (mk Γ) id) = f := by
    funext p
    obtain ⟨x, z⟩ := p
    obtain ⟨γ, hγ⟩ := exists_out_eq Γ x
    change f (Quotient.out (mk Γ x), z) = f (x, z)
    rw [hγ, hinv]
  rw [heq]
  exact hf

/-- A continuous function on `H × Y` invariant under `Γ` in the first variable, read at
representatives of `Γ \ H`, is continuous on `Γ \ H × Y`. -/
theorem continuous_out_prod' {Y E : Type*} [TopologicalSpace Y] [TopologicalSpace E]
    (f : H × Y → E) (hf : Continuous f)
    (hinv : ∀ (γ : Γ) (x : H) (y : Y), f ((γ : H) * x, y) = f (x, y)) :
    Continuous fun p : LeftCosetSpace Γ × Y => f (Quotient.out p.1, p.2) := by
  rw [← ((isOpenQuotientMap_mk Γ).prodMap IsOpenQuotientMap.id).continuous_comp_iff]
  have heq : ((fun p : LeftCosetSpace Γ × Y => f (Quotient.out p.1, p.2)) ∘
      Prod.map (mk Γ) id) = f := by
    funext p
    obtain ⟨x, y⟩ := p
    obtain ⟨γ, hγ⟩ := exists_out_eq Γ x
    change f (Quotient.out (mk Γ x), y) = f (x, y)
    rw [hγ, hinv]
  rw [heq]
  exact hf

end Basic

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H] [LocallyCompactSpace H]
  [PolishSpace H] (Γ : Subgroup H) (hΓ : IsDiscrete (Γ : Set H))
  [(Measure.haar : Measure H).IsMulRightInvariant]

include hΓ in
/-- For `Φ` invariant under the diagonal left action of `Γ`, the iterated integrals
`∫_{Γ \ H} ∫_H Φ(ξ, y) dy dξ` and `∫_{Γ \ H} ∫_H Φ(x, η) dx dη` agree, the quotient variable being
read at chosen representatives. -/
theorem integral_integral_swap_diagonal (Φ : H → H → ℂ)
    (hΦ : Continuous fun p : H × H => Φ p.1 p.2)
    (hinv : ∀ (γ : Γ) (x y : H), Φ ((γ : H) * x) ((γ : H) * y) = Φ x y)
    (hint : Integrable (fun p : LeftCosetSpace Γ × H =>
      Φ (Quotient.out p.1) (Quotient.out p.1 * p.2))
      ((haarQuotientMeasure Γ hΓ).prod (Measure.haar : Measure H))) :
    ∫ ξ, ∫ y, Φ (Quotient.out ξ) y ∂Measure.haar ∂haarQuotientMeasure Γ hΓ =
      ∫ η, ∫ x, Φ x (Quotient.out η) ∂Measure.haar ∂haarQuotientMeasure Γ hΓ := by
  let μ := haarQuotientMeasure Γ hΓ
  let ν := (Measure.haar : Measure H)
  have := ConstantTermAverage.isInvInvariant_of_isMulRightInvariant ν
  let := isLocallyFiniteMeasure_haarQuotientMeasure Γ hΓ
  let := discreteQuotientBorelSpace Γ hΓ
  let G₁ : LeftCosetSpace Γ × H → ℂ := fun p => Φ (Quotient.out p.1) (Quotient.out p.1 * p.2)
  let G₂ : LeftCosetSpace Γ × H → ℂ := fun p => Φ (Quotient.out p.1 * p.2⁻¹) (Quotient.out p.1)
  have hG₂c : Continuous G₂ := by
    refine continuous_out_prod Γ (fun p : H × H => Φ (p.1 * p.2⁻¹) p.1)
      (hΦ.comp ((continuous_fst.mul continuous_snd.inv).prodMk continuous_fst)) ?_
    intro γ x z
    simp only [mul_assoc]
    exact hinv γ _ _
  let S : LeftCosetSpace Γ × H → LeftCosetSpace Γ × H := fun p => (rightTranslate Γ p.2 p.1, p.2)
  have hS : MeasurePreserving S (μ.prod ν) (μ.prod ν) := by
    have hsk : MeasurePreserving (fun p : H × LeftCosetSpace Γ => (p.1, rightTranslate Γ p.1 p.2))
        (ν.prod μ) (ν.prod μ) := by
      refine MeasurePreserving.skew_product (MeasurePreserving.id ν) ?_ ?_
      · exact (continuous_smul.comp ((MulOpposite.continuous_op.comp continuous_fst).prodMk
          continuous_snd)).measurable
      · exact Filter.Eventually.of_forall fun z =>
          (measurePreserving_rightTranslate_haarQuotientMeasure Γ hΓ z).map_eq
    exact (Measure.measurePreserving_swap (μ := ν) (ν := μ)).comp
      (hsk.comp (Measure.measurePreserving_swap (μ := μ) (ν := ν)))
  have hG : ∀ p, G₂ (S p) = G₁ p := by
    rintro ⟨ξ, z⟩
    obtain ⟨x, rfl⟩ := mk_surjective Γ ξ
    change Φ (Quotient.out (rightTranslate Γ z (mk Γ x)) * z⁻¹)
      (Quotient.out (rightTranslate Γ z (mk Γ x))) = Φ (Quotient.out (mk Γ x)) _
    rw [rightTranslate_mk]
    obtain ⟨γ, hγ⟩ := exists_out_eq Γ (x * z)
    obtain ⟨δ, hδ⟩ := exists_out_eq Γ x
    rw [hγ, hδ, mul_assoc, mul_inv_cancel_right, hinv, mul_assoc, hinv]
  have hint₂ : Integrable G₂ (μ.prod ν) := by
    have h := hS.integrable_comp hG₂c.aestronglyMeasurable
    have hcomp : G₂ ∘ S = G₁ := funext hG
    rw [hcomp] at h
    exact h.mp hint
  calc ∫ ξ, ∫ y, Φ (Quotient.out ξ) y ∂ν ∂μ = ∫ ξ, ∫ z, G₁ (ξ, z) ∂ν ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        exact (integral_mul_left_eq_self (fun y => Φ (Quotient.out ξ) y) (Quotient.out ξ) :
          ∫ x, Φ (Quotient.out ξ) (Quotient.out ξ * x) ∂ν = _).symm
    _ = ∫ z, ∫ ξ, G₁ (ξ, z) ∂μ ∂ν := integral_integral_swap hint
    _ = ∫ z, ∫ η, G₂ (η, z) ∂μ ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        dsimp only
        have hmp := measurePreserving_rightTranslate_haarQuotientMeasure Γ hΓ z
        conv_rhs => rw [← (hmp.integral_comp (rightTranslateHomeomorph Γ z).measurableEmbedding)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => (hG (ξ, z)).symm)
    _ = ∫ η, ∫ z, G₂ (η, z) ∂ν ∂μ := (integral_integral_swap hint₂).symm
    _ = ∫ η, ∫ x, Φ x (Quotient.out η) ∂ν ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
        have h := integral_div_left_eq_self (fun x => Φ x (Quotient.out η)) ν (Quotient.out η)
        simp only [div_eq_mul_inv] at h
        exact h

end Langlands.Global.LeftCosetSpace
