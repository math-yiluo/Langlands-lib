import Langlands.Analysis.Local.ProductQuotientMeasures
import Langlands.TraceFormula.TwistedOrbital

/-! # Exact orbital integration through an equivariant product decomposition -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.TraceFormula

open MeasureTheory MeasureTheory.Measure Topology
open Langlands.QuotientIntegration

section Product

variable {G₁ G₂ G : Type*} [Group G₁] [Group G₂] [Group G]
  [TopologicalSpace G₁] [TopologicalSpace G₂] [TopologicalSpace G]
  (D : G₁ × G₂ ≃ₜ* G)
  (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (θ : G →* G)
  (hθ : ∀ p, θ (D p) = D (θ₁ p.1, θ₂ p.2)) (δ : G)

local notation "C₁" => twistedCentralizer θ₁ (Prod.fst (D.symm δ))
local notation "C₂" => twistedCentralizer θ₂ (Prod.snd (D.symm δ))
local notation "C" => twistedCentralizer θ δ

include hθ in
private theorem twistedConj_product (p z : G₁ × G₂) :
    twistedConj θ (D p) (D z) =
      D (twistedConj θ₁ p.1 z.1, twistedConj θ₂ p.2 z.2) := by
  change (D p)⁻¹ * D z * θ (D p) = D (p⁻¹ * z * (θ₁ p.1, θ₂ p.2))
  rw [map_mul, map_mul, map_inv, hθ]

include hθ in
private theorem twistedConj_product_symm (p : G₁ × G₂) :
    D.symm (twistedConj θ (D p) δ) =
      (twistedConj θ₁ p.1 (D.symm δ).1, twistedConj θ₂ p.2 (D.symm δ).2) := by
  apply D.injective
  simpa only [D.apply_symm_apply] using twistedConj_product D θ₁ θ₂ θ hθ p (D.symm δ)

include hθ in
private theorem mem_twistedCentralizer_product (p : G₁ × G₂) :
    D p ∈ C ↔ p ∈ Subgroup.prod C₁ C₂ := by
  change twistedConj θ (D p) δ = δ ↔
    (twistedConj θ₁ p.1 (D.symm δ).1 = (D.symm δ).1 ∧
      twistedConj θ₂ p.2 (D.symm δ).2 = (D.symm δ).2)
  rw [← D.symm.injective.eq_iff, twistedConj_product_symm D θ₁ θ₂ θ hθ δ, Prod.ext_iff]

variable [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]

/-- The product of the factor centralizers identifies with the actual centralizer. -/
def twistedCentralizerProductEquiv : Subgroup.prod C₁ C₂ ≃ₜ* C :=
  subgroupContinuousMulEquiv D _ _ (mem_twistedCentralizer_product D θ₁ θ₂ θ hθ δ)

private def twistedCentralizerProductQuotient :
    LeftQuotient (Subgroup.prod C₁ C₂) ≃ₜ LeftQuotient C :=
  Homeomorph.Quotient.congr D.toHomeomorph (by
    intro x y
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change (y * x⁻¹ ∈ Subgroup.prod C₁ C₂) ↔ D y * (D x)⁻¹ ∈ C
    rw [← map_inv, ← map_mul]
    exact (mem_twistedCentralizer_product D θ₁ θ₂ θ hθ δ _).symm)

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] in
@[simp] private theorem twistedCentralizerProductQuotient_mk (p : G₁ × G₂) :
    twistedCentralizerProductQuotient D θ₁ θ₂ θ hθ δ (Quotient.mk _ p) =
      Quotient.mk _ (D p) := rfl

/-- The actual twisted quotient is identified with the two factor quotients
through their canonical product quotient. -/
def twistedOrbitProductHomeomorph :
    LeftQuotient C₁ × LeftQuotient C₂ ≃ₜ LeftQuotient C :=
  (leftQuotientProdHomeomorph C₁ C₂).symm.trans
    (twistedCentralizerProductQuotient D θ₁ θ₂ θ hθ δ)

@[simp] theorem twistedOrbitProductHomeomorph_mk (p : G₁ × G₂) :
    twistedOrbitProductHomeomorph D θ₁ θ₂ θ hθ δ (Quotient.mk _ p.1, Quotient.mk _ p.2) =
      Quotient.mk _ (D p) := by
  change twistedCentralizerProductQuotient D θ₁ θ₂ θ hθ δ
      ((leftQuotientProdHomeomorph C₁ C₂).symm (Quotient.mk _ p.1, Quotient.mk _ p.2)) = _
  rw [← leftQuotientProdHomeomorph_mk C₁ C₂ p, Homeomorph.symm_apply_apply,
    twistedCentralizerProductQuotient_mk]

include hθ in
private theorem twistedOrbitFunction_product (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ)
    (q : LeftQuotient C₁) (r : LeftQuotient C₂) :
    twistedOrbitFunction θ δ (fun x => f₁ (D.symm x).1 * f₂ (D.symm x).2)
        (twistedOrbitProductHomeomorph D θ₁ θ₂ θ hθ δ (q, r)) =
      twistedOrbitFunction θ₁ (D.symm δ).1 f₁ q *
        twistedOrbitFunction θ₂ (D.symm δ).2 f₂ r := by
  induction q using Quotient.inductionOn with
  | h x =>
    induction r using Quotient.inductionOn with
    | h y =>
      rw [twistedOrbitProductHomeomorph_mk D θ₁ θ₂ θ hθ δ (x, y)]
      change f₁ (D.symm (twistedConj θ (D (x, y)) δ)).1 *
        f₂ (D.symm (twistedConj θ (D (x, y)) δ)).2 =
        f₁ (twistedConj θ₁ x (D.symm δ).1) * f₂ (twistedConj θ₂ y (D.symm δ).2)
      rw [twistedConj_product_symm D θ₁ θ₂ θ hθ δ]

section Quotient

variable [MeasurableSpace (LeftQuotient (twistedCentralizer θ₁ (D.symm δ).1))]
  [BorelSpace (LeftQuotient (twistedCentralizer θ₁ (D.symm δ).1))]
  [MeasurableSpace (LeftQuotient (twistedCentralizer θ₂ (D.symm δ).2))]
  [BorelSpace (LeftQuotient (twistedCentralizer θ₂ (D.symm δ).2))]
  [MeasurableSpace (LeftQuotient (twistedCentralizer θ δ))]
  [BorelSpace (LeftQuotient (twistedCentralizer θ δ))]
  (ν₁ : Measure (LeftQuotient (twistedCentralizer θ₁ (D.symm δ).1)))
  (ν₂ : Measure (LeftQuotient (twistedCentralizer θ₂ (D.symm δ).2)))

/-- Exact transport of the factor orbital quotient measures. -/
def twistedOrbitProductMeasure : Measure (LeftQuotient C) :=
  Measure.map (α := LeftQuotient C₁ × LeftQuotient C₂) (β := LeftQuotient C)
    (twistedOrbitProductHomeomorph D θ₁ θ₂ θ hθ δ) (ν₁.prod ν₂)

variable [SecondCountableTopology (LeftQuotient (twistedCentralizer θ₁ (D.symm δ).1))]
  [SFinite ν₁] [SFinite ν₂]

set_option maxHeartbeats 600000 in
/-- The twisted orbital integral of the transported tensor product is the
product of the two factor orbital integrals. -/
theorem twistedOrbitalIntegral_product (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ) :
    twistedOrbitalIntegral θ δ (twistedOrbitProductMeasure D θ₁ θ₂ θ hθ δ ν₁ ν₂)
        (fun x => f₁ (D.symm x).1 * f₂ (D.symm x).2) =
      twistedOrbitalIntegral θ₁ (D.symm δ).1 ν₁ f₁ *
        twistedOrbitalIntegral θ₂ (D.symm δ).2 ν₂ f₂ := by
  let e := twistedOrbitProductHomeomorph D θ₁ θ₂ θ hθ δ
  calc
    _ = ∫ p, twistedOrbitFunction θ δ
        (fun x => f₁ (D.symm x).1 * f₂ (D.symm x).2) (e p) ∂ν₁.prod ν₂ :=
      integral_map_equiv e.toMeasurableEquiv _
    _ = ∫ p : LeftQuotient C₁ × LeftQuotient C₂,
        twistedOrbitFunction θ₁ (D.symm δ).1 f₁ p.1 *
          twistedOrbitFunction θ₂ (D.symm δ).2 f₂ p.2 ∂ν₁.prod ν₂ := by
      refine integral_congr_ae (Filter.Eventually.of_forall ?_)
      rintro ⟨q, r⟩
      exact twistedOrbitFunction_product D θ₁ θ₂ θ hθ δ f₁ f₂ q r
    _ = _ := integral_prod_mul (twistedOrbitFunction θ₁ (D.symm δ).1 f₁)
      (twistedOrbitFunction θ₂ (D.symm δ).2 f₂)

end Quotient

section Compatible

variable [IsTopologicalGroup G] [T2Space G₂]
  [SecondCountableTopology G₁] [SecondCountableTopology G₂]
  [LocallyCompactSpace G₁] [LocallyCompactSpace G₂]
  [MeasurableSpace G₁] [BorelSpace G₁] [MeasurableSpace G₂] [BorelSpace G₂]
  [MeasurableSpace G] [BorelSpace G]
  (μ₁ : Measure G₁) (μ₂ : Measure G₂)
  (μC₁ : Measure (twistedCentralizer θ₁ (D.symm δ).1))
  (μC₂ : Measure (twistedCentralizer θ₂ (D.symm δ).2))

/-- Product normalization on the actual twisted centralizer of `δ`. -/
def twistedCentralizerProductMeasure : Measure C :=
  Measure.map (α := Subgroup.prod C₁ C₂) (β := C)
    (twistedCentralizerProductEquiv D θ₁ θ₂ θ hθ δ)
    (productSubgroupMeasure C₁ C₂ μC₁ μC₂)

variable [SigmaFinite μC₁] [SigmaFinite μC₂] [IsMulRightInvariant μC₁] [IsMulRightInvariant μC₂]

instance twistedCentralizerProductMeasure_rightInvariant :
    IsMulRightInvariant (twistedCentralizerProductMeasure D θ₁ θ₂ θ hθ δ μC₁ μC₂) :=
  isMulRightInvariant_map (twistedCentralizerProductEquiv D θ₁ θ₂ θ hθ δ) _

instance twistedCentralizerProductMeasure_openPos
    [IsOpenPosMeasure μC₁] [IsOpenPosMeasure μC₂] :
    IsOpenPosMeasure (twistedCentralizerProductMeasure D θ₁ θ₂ θ hθ δ μC₁ μC₂) := by
  let : BorelSpace C₁ := Subtype.borelSpace (· ∈ C₁)
  let : BorelSpace C₂ := Subtype.borelSpace (· ∈ C₂)
  let : SecondCountableTopology C₁ := TopologicalSpace.Subtype.secondCountableTopology (C₁ : Set G₁)
  let eP := (prodSubgroupHomeomorph C₁ C₂).symm
  let eC := twistedCentralizerProductEquiv D θ₁ θ₂ θ hθ δ
  have : IsOpenPosMeasure (productSubgroupMeasure C₁ C₂ μC₁ μC₂) :=
    eP.continuous.isOpenPosMeasure_map eP.surjective (μ := μC₁.prod μC₂)
  exact eC.continuous.isOpenPosMeasure_map eC.surjective

variable [IsFiniteMeasureOnCompacts μ₁] [IsFiniteMeasureOnCompacts μ₂]
  [IsFiniteMeasureOnCompacts μC₁] [IsFiniteMeasureOnCompacts μC₂]
  [MeasurableSpace (LeftQuotient (twistedCentralizer θ₁ (D.symm δ).1))]
  [BorelSpace (LeftQuotient (twistedCentralizer θ₁ (D.symm δ).1))]
  [MeasurableSpace (LeftQuotient (twistedCentralizer θ₂ (D.symm δ).2))]
  [BorelSpace (LeftQuotient (twistedCentralizer θ₂ (D.symm δ).2))]
  [MeasurableSpace (LeftQuotient (twistedCentralizer θ δ))]
  [BorelSpace (LeftQuotient (twistedCentralizer θ δ))]
  (ν₁ : Measure (LeftQuotient (twistedCentralizer θ₁ (D.symm δ).1)))
  (ν₂ : Measure (LeftQuotient (twistedCentralizer θ₂ (D.symm δ).2)))

instance twistedCentralizerProductMeasure_finiteOnCompacts :
    IsFiniteMeasureOnCompacts (twistedCentralizerProductMeasure D θ₁ θ₂ θ hθ δ μC₁ μC₂) :=
  IsFiniteMeasureOnCompacts.map _ (twistedCentralizerProductEquiv D θ₁ θ₂ θ hθ δ).toHomeomorph

set_option maxHeartbeats 600000 in
/-- The tensor product quotient measure satisfies the Weil formula for the
corresponding transported ambient and centralizer measures. -/
theorem twistedOrbitProductMeasure_isCompatible
    (h₁ : IsClosed (C₁ : Set G₁)) (h₂ : IsClosed (C₂ : Set G₂))
    (hc₁ : IsCompatible C₁ μ₁ μC₁ ν₁) (hc₂ : IsCompatible C₂ μ₂ μC₂ ν₂) :
    IsCompatible C (Measure.map D (μ₁.prod μ₂))
      (twistedCentralizerProductMeasure D θ₁ θ₂ θ hθ δ μC₁ μC₂)
      (twistedOrbitProductMeasure D θ₁ θ₂ θ hθ δ ν₁ ν₂) := by
  let : MeasurableSpace (LeftQuotient (Subgroup.prod C₁ C₂)) := borel _
  let : BorelSpace (LeftQuotient (Subgroup.prod C₁ C₂)) := ⟨rfl⟩
  let := (leftQuotient_isOpenQuotientMap C₁).secondCountableTopology
  let eP := (leftQuotientProdHomeomorph C₁ C₂).symm
  let eQ := twistedCentralizerProductQuotient D θ₁ θ₂ θ hθ δ
  let eC := twistedCentralizerProductEquiv D θ₁ θ₂ θ hθ δ
  have hc := productQuotientMeasure_isCompatible C₁ C₂ μC₁ μC₂ h₁ h₂ μ₁ μ₂ ν₁ ν₂ hc₁ hc₂
  have ht := isCompatible_map_equiv D (Subgroup.prod C₁ C₂) C eC (fun _ => rfl) eQ
    (twistedCentralizerProductQuotient_mk D θ₁ θ₂ θ hθ δ) _ _ _ hc
  change IsCompatible C (Measure.map D (μ₁.prod μ₂))
    (twistedCentralizerProductMeasure D θ₁ θ₂ θ hθ δ μC₁ μC₂)
    (Measure.map eQ (Measure.map eP (ν₁.prod ν₂))) at ht
  rw [Measure.map_map eQ.continuous.measurable eP.continuous.measurable] at ht
  exact ht

/-- Compatible factor measures give both the transported compatible measure
and the product orbital-integral identity for every pair of factor functions. -/
def TwistedOrbitalProductStatement : Prop :=
  ∀ [SecondCountableTopology G₁] [T2Space G₂]
    [LocallyCompactSpace G₁] [LocallyCompactSpace G₂]
    [IsFiniteMeasureOnCompacts μ₁] [IsFiniteMeasureOnCompacts μ₂]
    [IsFiniteMeasureOnCompacts μC₁] [IsFiniteMeasureOnCompacts μC₂]
    [BorelSpace (LeftQuotient C₁)] [BorelSpace (LeftQuotient C₂)]
    [BorelSpace (LeftQuotient C)],
  IsClosed (C₁ : Set G₁) → IsClosed (C₂ : Set G₂) →
  IsCompatible C₁ μ₁ μC₁ ν₁ → IsCompatible C₂ μ₂ μC₂ ν₂ →
  IsCompatible C (Measure.map D (μ₁.prod μ₂))
    (twistedCentralizerProductMeasure D θ₁ θ₂ θ hθ δ μC₁ μC₂)
    (twistedOrbitProductMeasure D θ₁ θ₂ θ hθ δ ν₁ ν₂) ∧
  ∀ (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ),
    twistedOrbitalIntegral θ δ (twistedOrbitProductMeasure D θ₁ θ₂ θ hθ δ ν₁ ν₂)
        (fun x => f₁ (D.symm x).1 * f₂ (D.symm x).2) =
      twistedOrbitalIntegral θ₁ (D.symm δ).1 ν₁ f₁ *
        twistedOrbitalIntegral θ₂ (D.symm δ).2 ν₂ f₂

omit [SecondCountableTopology G₁] [T2Space G₂]
  [LocallyCompactSpace G₁] [LocallyCompactSpace G₂]
  [IsFiniteMeasureOnCompacts μ₁] [IsFiniteMeasureOnCompacts μ₂]
  [IsFiniteMeasureOnCompacts μC₁] [IsFiniteMeasureOnCompacts μC₂]
  [BorelSpace (LeftQuotient (twistedCentralizer θ₁ (D.symm δ).1))]
  [BorelSpace (LeftQuotient (twistedCentralizer θ₂ (D.symm δ).2))]
  [BorelSpace (LeftQuotient (twistedCentralizer θ δ))] in
set_option maxHeartbeats 600000 in
theorem twistedOrbitalProduct :
    TwistedOrbitalProductStatement D θ₁ θ₂ θ hθ δ μ₁ μ₂ μC₁ μC₂ ν₁ ν₂ := by
  intro _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ hc₁ hc₂
  let := leftQuotient_locallyCompactSpace C₁
  let := leftQuotient_locallyCompactSpace C₂
  let := (leftQuotient_isOpenQuotientMap C₁).secondCountableTopology
  let := (leftQuotient_isOpenQuotientMap C₂).secondCountableTopology
  let := hc₁.regular
  let := hc₂.regular
  exact ⟨twistedOrbitProductMeasure_isCompatible D θ₁ θ₂ θ hθ δ μ₁ μ₂ μC₁ μC₂ ν₁ ν₂
      h₁ h₂ hc₁ hc₂,
    twistedOrbitalIntegral_product D θ₁ θ₂ θ hθ δ ν₁ ν₂⟩

end Compatible

end Product

end Langlands.TraceFormula
