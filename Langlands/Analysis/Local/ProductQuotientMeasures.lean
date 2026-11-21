import Langlands.Analysis.Local.LeftQuotientProduct
import Langlands.Analysis.Local.QuotientComplex
import Mathlib.MeasureTheory.Integral.Prod

/-! # Compatibility of products of Weil quotient measures -/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure Topology
open scoped CompactlySupported

universe u₁ u₂

private def compactQuotientAverage {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H] (μH : Measure H)
    [IsMulRightInvariant μH] [IsFiniteMeasureOnCompacts μH] (f : C_c(G, ℂ)) :
    C_c(LeftQuotient H, ℂ) :=
  complexifyCompactMap (quotientAverageRealPositive H hH μH) f

private theorem compactQuotientAverage_eq {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H] (μH : Measure H)
    [IsMulRightInvariant μH] [IsFiniteMeasureOnCompacts μH] (f : C_c(G, ℂ)) :
    (compactQuotientAverage H hH μH f : LeftQuotient H → ℂ) = quotientAverage H μH f :=
  complexifyCompactMap_eq_quotientAverage H μH
    (quotientAverageRealPositive H hH μH) (fun _ _ => rfl) f
    (integrable_subgroup_mul_of_hasCompactSupport H hH μH f f.continuous f.hasCompactSupport)

local instance subgroupSecondCountable {G : Type*} [Group G] [TopologicalSpace G]
    [SecondCountableTopology G] (H : Subgroup G) : SecondCountableTopology H :=
  TopologicalSpace.Subtype.secondCountableTopology (H : Set G)

local instance subgroupBorelSpace {G : Type*} [Group G] [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) : BorelSpace H :=
  Subtype.borelSpace (· ∈ H)

section Product

variable {G₁ : Type u₁} {G₂ : Type u₂} [Group G₁] [Group G₂]
  [TopologicalSpace G₁] [TopologicalSpace G₂] (A : Subgroup G₁) (B : Subgroup G₂)

private theorem isClosed_prodSubgroup (hA : IsClosed (A : Set G₁))
    (hB : IsClosed (B : Set G₂)) : IsClosed (A.prod B : Set (G₁ × G₂)) :=
  hA.prod hB

variable [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]

private def firstAverageChart :
    LeftQuotient (A.prod (⊥ : Subgroup G₂)) ≃ₜ LeftQuotient A × G₂ :=
  (leftQuotientProdHomeomorph A ⊥).trans (Homeomorph.prodCongr (Homeomorph.refl _)
    trivialQuotientHomeomorph)

private theorem firstAverageChart_mk (x : G₁ × G₂) :
    firstAverageChart A (G₂ := G₂) (Quotient.mk _ x) =
      ((Quotient.mk _ x.1 : LeftQuotient A), x.2) := rfl

variable [MeasurableSpace G₁] [BorelSpace G₁] [MeasurableSpace G₂] [BorelSpace G₂]
variable (μA : Measure A) (μB : Measure B)

/-- The product of the supplied subgroup measures in the actual subgroup `A.prod B`. -/
def productSubgroupMeasure : Measure (A.prod B) :=
  Measure.map (prodSubgroupHomeomorph A B).symm (μA.prod μB)

variable [SecondCountableTopology G₁] [SecondCountableTopology G₂]
  [SigmaFinite μA] [SigmaFinite μB]

instance productSubgroupMeasure_rightInvariant
    [IsMulRightInvariant μA] [IsMulRightInvariant μB] :
    IsMulRightInvariant (productSubgroupMeasure A B μA μB) :=
  isMulRightInvariant_map (prodSubgroupHomeomorph A B).symm (μA.prod μB)

instance productSubgroupMeasure_finiteOnCompacts
    [IsFiniteMeasureOnCompacts μA] [IsFiniteMeasureOnCompacts μB] :
    IsFiniteMeasureOnCompacts (productSubgroupMeasure A B μA μB) :=
  IsFiniteMeasureOnCompacts.map (μA.prod μB) (prodSubgroupHomeomorph A B).symm.toHomeomorph

variable [IsFiniteMeasureOnCompacts μA] [IsFiniteMeasureOnCompacts μB]

omit [SecondCountableTopology G₁] [SigmaFinite μA] in
private theorem integrable_product_fiber (hA : IsClosed (A : Set G₁))
    (hB : IsClosed (B : Set G₂)) (f : C_c(G₁ × G₂, ℂ)) (x : G₁) (y : G₂) :
    Integrable (fun p : A × B => f (p.1.val * x, p.2.val * y)) (μA.prod μB) := by
  have hj : IsClosedEmbedding (fun p : A × B => (p.1.val, p.2.val) * (x, y)) :=
    (Homeomorph.mulRight (x, y)).isClosedEmbedding.comp
      (hA.isClosedEmbedding_subtypeVal.prodMap hB.isClosedEmbedding_subtypeVal)
  exact (f.continuous.comp hj.continuous).integrable_of_hasCompactSupport
    (f.hasCompactSupport.comp_isClosedEmbedding hj)

variable [T2Space G₁] [T2Space G₂] [LocallyCompactSpace G₁] [LocallyCompactSpace G₂]
  [IsMulRightInvariant μA] [IsMulRightInvariant μB]

private def firstAverage (hA : IsClosed (A : Set G₁)) (f : C_c(G₁ × G₂, ℂ)) :
    C_c(LeftQuotient A × G₂, ℂ) :=
  let a := compactQuotientAverage _ (isClosed_prodSubgroup A ⊥ hA isClosed_singleton)
    (productSubgroupMeasure A ⊥ μA (Measure.dirac 1)) f
  let e := (firstAverageChart A (G₂ := G₂)).symm
  ⟨⟨a ∘ e, a.continuous.comp e.continuous⟩, a.hasCompactSupport.comp_homeomorph e⟩

omit [SecondCountableTopology G₁] [T2Space G₁] in
private theorem firstAverage_apply (hA : IsClosed (A : Set G₁))
    (f : C_c(G₁ × G₂, ℂ)) (x : G₁) (y : G₂) :
    firstAverage A μA hA f (Quotient.mk _ x, y) =
      ∫ a : A, f (a.val * x, y) ∂μA := by
  let H := A.prod (⊥ : Subgroup G₂)
  let μH := productSubgroupMeasure A (⊥ : Subgroup G₂) μA (Measure.dirac 1)
  let P := compactQuotientAverage H (isClosed_prodSubgroup A ⊥ hA isClosed_singleton) μH f
  have hq : (firstAverageChart A (G₂ := G₂)).symm (Quotient.mk _ x, y) =
      (Quotient.mk _ (x, y) : LeftQuotient H) := by
    apply (firstAverageChart A (G₂ := G₂)).injective
    rw [Homeomorph.apply_symm_apply, firstAverageChart_mk]
  change (P : LeftQuotient H → ℂ) _ = _
  rw [hq, compactQuotientAverage_eq, quotientAverage_mk]
  let e := (prodSubgroupHomeomorph A (⊥ : Subgroup G₂)).symm
  calc
    (∫ h : H, f (h.val * (x, y)) ∂μH) =
        ∫ p : A × (⊥ : Subgroup G₂), f (p.1.val * x, p.2.val * y)
          ∂μA.prod (Measure.dirac 1) :=
      integral_map_equiv e.toHomeomorph.toMeasurableEquiv _
    _ = ∫ a : A, ∫ b : (⊥ : Subgroup G₂), f (a.val * x, b.val * y)
          ∂Measure.dirac 1 ∂μA :=
      integral_prod _ (integrable_product_fiber A ⊥ μA (Measure.dirac 1) hA
        isClosed_singleton f x y)
    _ = ∫ a : A, f (a.val * x, y) ∂μA := by
      simp

omit [SecondCountableTopology G₁] [T2Space G₁] in
private theorem quotientAverage_product_mk
    (hA : IsClosed (A : Set G₁)) (hB : IsClosed (B : Set G₂))
    (f : C_c(G₁ × G₂, ℂ)) (x : G₁) (y : G₂) :
    quotientAverage (A.prod B) (productSubgroupMeasure A B μA μB) f
      (Quotient.mk _ (x, y)) =
      ∫ b : B, firstAverage A μA hA f (Quotient.mk _ x, b.val * y) ∂μB := by
  rw [quotientAverage_mk]
  let e := (prodSubgroupHomeomorph A B).symm
  calc
    (∫ h : A.prod B, f (h.val * (x, y)) ∂productSubgroupMeasure A B μA μB) =
        ∫ p : A × B, f (p.1.val * x, p.2.val * y) ∂μA.prod μB :=
      integral_map_equiv e.toHomeomorph.toMeasurableEquiv _
    _ = ∫ b : B, ∫ a : A, f (a.val * x, b.val * y) ∂μA ∂μB :=
      integral_prod_symm _ (integrable_product_fiber A B μA μB hA hB f x y)
    _ = _ := by simp_rw [firstAverage_apply]

variable [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]
  [MeasurableSpace (LeftQuotient B)] [BorelSpace (LeftQuotient B)]
  [MeasurableSpace (LeftQuotient (A.prod B))] [BorelSpace (LeftQuotient (A.prod B))]

/-- The pushforward of the product measure on the two left quotients. -/
def productQuotientMeasure (νA : Measure (LeftQuotient A))
    (νB : Measure (LeftQuotient B)) : Measure (LeftQuotient (A.prod B)) :=
  Measure.map (leftQuotientProdHomeomorph A B).symm (νA.prod νB)

private def compactSliceLeft {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T1Space X] (f : C_c(X × Y, ℂ)) (x : X) : C_c(Y, ℂ) :=
  ⟨⟨fun y => f (x, y), f.continuous.comp (continuous_const.prodMk continuous_id)⟩,
    f.hasCompactSupport.comp_isClosedEmbedding ⟨isEmbedding_prodMkRight x, by
      have h : Set.range (Prod.mk x : Y → X × Y) = Prod.fst ⁻¹' {x} := by
        ext p
        simp [Prod.ext_iff, eq_comm]
      rw [h]
      exact isClosed_singleton.preimage continuous_fst⟩⟩

private def compactSliceRight {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T1Space Y] (f : C_c(X × Y, ℂ)) (y : Y) : C_c(X, ℂ) :=
  ⟨⟨fun x => f (x, y), f.continuous.comp (continuous_id.prodMk continuous_const)⟩,
    f.hasCompactSupport.comp_isClosedEmbedding ⟨isEmbedding_prodMkLeft y, by
      have h : Set.range (fun x : X => (x, y)) = Prod.snd ⁻¹' {y} := by
        ext p
        simp [Prod.ext_iff, eq_comm]
      rw [h]
      exact isClosed_singleton.preimage continuous_snd⟩⟩

omit [T2Space G₁] in
set_option maxHeartbeats 700000 in
/-- The product of compatible quotient measures is compatible for the actual product
group, with the subgroup measure transported from the product of subgroup measures. -/
theorem productQuotientMeasure_isCompatible
    (hA : IsClosed (A : Set G₁)) (hB : IsClosed (B : Set G₂))
    (μ₁ : Measure G₁) (μ₂ : Measure G₂)
    [IsFiniteMeasureOnCompacts μ₁] [IsFiniteMeasureOnCompacts μ₂]
    (νA : Measure (LeftQuotient A)) (νB : Measure (LeftQuotient B))
    (hcA : IsCompatible A μ₁ μA νA) (hcB : IsCompatible B μ₂ μB νB) :
    IsCompatible (A.prod B) (μ₁.prod μ₂) (productSubgroupMeasure A B μA μB)
      (productQuotientMeasure A B νA νB) := by
  let e := leftQuotientProdHomeomorph A B
  let := leftQuotient_t2Space A hA
  let := leftQuotient_t2Space B hB
  let := leftQuotient_locallyCompactSpace A
  let := leftQuotient_locallyCompactSpace B
  let := (leftQuotient_isOpenQuotientMap A).secondCountableTopology
  let := (leftQuotient_isOpenQuotientMap B).secondCountableTopology
  let := hcA.regular
  let := hcB.regular
  let : (νA.prod νB).Regular := inferInstance
  have hNZ : νA.prod νB ≠ 0 := by
    intro he
    have hu : νA.prod νB Set.univ = 0 := measure_univ_eq_zero.2 he
    rw [← Set.univ_prod_univ, Measure.prod_prod] at hu
    exact (mul_ne_zero ((not_congr measure_univ_eq_zero).2 hcA.nonzero)
      ((not_congr measure_univ_eq_zero).2 hcB.nonzero)) hu
  have hClosed := isClosed_prodSubgroup A B hA hB
  have hν : (productQuotientMeasure A B νA νB).Regular := Measure.Regular.map e.symm
  let := hν
  refine
    { nonzero := (Measure.map_ne_zero_iff e.symm.continuous.measurable.aemeasurable).2 hNZ
      regular := hν
      right_invariant := ?_
      averaging_integrable := ?_
      integral_formula := ?_ }
  · intro p
    refine ⟨(rightTranslate _ p).continuous.measurable, ?_⟩
    have hcomm : rightTranslate (A.prod B) p ∘ e.symm =
        e.symm ∘ Prod.map (rightTranslate A p.1) (rightTranslate B p.2) := by
      funext q
      apply e.injective
      change e (rightTranslate (A.prod B) p (e.symm q)) =
        e (e.symm (Prod.map (rightTranslate A p.1) (rightTranslate B p.2) q))
      simp only [e, leftQuotientProdHomeomorph_rightTranslate, Homeomorph.apply_symm_apply]
    have hpres := (hcA.right_invariant p.1).prod (hcB.right_invariant p.2)
    rw [productQuotientMeasure,
      Measure.map_map (rightTranslate _ p).continuous.measurable e.symm.continuous.measurable,
      hcomm, ← Measure.map_map e.symm.continuous.measurable hpres.measurable, hpres.map_eq]
  · intro f hf hfc
    let F : C_c(G₁ × G₂, ℂ) := ⟨⟨f, hf⟩, hfc⟩
    let Q := compactQuotientAverage (A.prod B) hClosed (productSubgroupMeasure A B μA μB) F
    change Integrable (quotientAverage (A.prod B) (productSubgroupMeasure A B μA μB) F) _
    rw [← compactQuotientAverage_eq _ hClosed _ F]
    exact Q.continuous.integrable_of_hasCompactSupport Q.hasCompactSupport
  · intro f hf hfc
    let F : C_c(G₁ × G₂, ℂ) := ⟨⟨f, hf⟩, hfc⟩
    let P := firstAverage A μA hA F
    let Q := compactQuotientAverage (A.prod B) hClosed (productSubgroupMeasure A B μA μB) F
    have hiter (q : LeftQuotient A) (r : LeftQuotient B) :
        Q (e.symm (q, r)) =
          quotientAverage B μB (compactSliceLeft P q) r := by
      induction q using Quotient.inductionOn with
      | h x =>
        induction r using Quotient.inductionOn with
        | h y =>
          have he : e.symm (Quotient.mk _ x, Quotient.mk _ y) =
              Quotient.mk _ (x, y) := e.symm_apply_eq.mpr
            (leftQuotientProdHomeomorph_mk A B (x, y)).symm
          change (Q : LeftQuotient (A.prod B) → ℂ) _ = _
          rw [he, compactQuotientAverage_eq _ hClosed _ F, quotientAverage_mk (H := B)]
          exact quotientAverage_product_mk A B μA μB hA hB F x y
    have hQ : Integrable (fun p => Q (e.symm p)) (νA.prod νB) :=
      (Q.continuous.comp e.symm.continuous).integrable_of_hasCompactSupport
        (Q.hasCompactSupport.comp_homeomorph e.symm)
    have hP : Integrable P (νA.prod μ₂) :=
      P.continuous.integrable_of_hasCompactSupport P.hasCompactSupport
    have hF : Integrable F (μ₁.prod μ₂) := hf.integrable_of_hasCompactSupport hfc
    change (∫ q, quotientAverage (A.prod B) (productSubgroupMeasure A B μA μB) F q
      ∂productQuotientMeasure A B νA νB) = _
    rw [← compactQuotientAverage_eq _ hClosed _ F]
    calc
      (∫ q, Q q ∂productQuotientMeasure A B νA νB) =
          ∫ p, Q (e.symm p) ∂νA.prod νB := integral_map_equiv e.symm.toMeasurableEquiv _
      _ = ∫ q, ∫ r, Q (e.symm (q, r)) ∂νB ∂νA := integral_prod _ hQ
      _ = ∫ q, ∫ y, P (q, y) ∂μ₂ ∂νA := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun q => ?_
        simp_rw [hiter]
        exact hcB.integral_formula _ (compactSliceLeft P q).continuous
          (compactSliceLeft P q).hasCompactSupport
      _ = ∫ p, P p ∂νA.prod μ₂ := (integral_prod P hP).symm
      _ = ∫ y, ∫ q, P (q, y) ∂νA ∂μ₂ := integral_prod_symm P hP
      _ = ∫ y, ∫ x, F (x, y) ∂μ₁ ∂μ₂ := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun y => ?_
        have hp : (fun q => P (q, y)) = quotientAverage A μA (compactSliceRight F y) := by
          funext q
          induction q using Quotient.inductionOn with
          | h x =>
            rw [quotientAverage_mk]
            exact firstAverage_apply A μA hA F x y
        change (∫ q, P (q, y) ∂νA) = ∫ x, F (x, y) ∂μ₁
        rw [hp]
        exact hcA.integral_formula _ (compactSliceRight F y).continuous
          (compactSliceRight F y).hasCompactSupport
      _ = ∫ x, f x ∂μ₁.prod μ₂ := (integral_prod_symm F hF).symm

end Product

/-- Product compatibility for actual Weil measures of two closed subgroups. -/
def ProductQuotientCompatibilityStatement : Prop :=
  ∀ (G₁ : Type u₁) (G₂ : Type u₂) [Group G₁] [Group G₂]
    [TopologicalSpace G₁] [TopologicalSpace G₂]
    [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
    [T2Space G₁] [T2Space G₂] [SecondCountableTopology G₁] [SecondCountableTopology G₂]
    [LocallyCompactSpace G₁] [LocallyCompactSpace G₂]
    [MeasurableSpace G₁] [MeasurableSpace G₂] [BorelSpace G₁] [BorelSpace G₂]
    (A : Subgroup G₁) (B : Subgroup G₂),
    IsClosed (A : Set G₁) → IsClosed (B : Set G₂) →
    ∀ [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]
      [MeasurableSpace (LeftQuotient B)] [BorelSpace (LeftQuotient B)]
      [MeasurableSpace (LeftQuotient (A.prod B))] [BorelSpace (LeftQuotient (A.prod B))]
      (μ₁ : Measure G₁) (μ₂ : Measure G₂)
      [IsFiniteMeasureOnCompacts μ₁] [IsFiniteMeasureOnCompacts μ₂]
      (μA : Measure A) (μB : Measure B) [IsMulRightInvariant μA] [IsMulRightInvariant μB]
      [IsFiniteMeasureOnCompacts μA] [IsFiniteMeasureOnCompacts μB]
      [SigmaFinite μA] [SigmaFinite μB]
      (νA : Measure (LeftQuotient A)) (νB : Measure (LeftQuotient B)),
      IsCompatible A μ₁ μA νA → IsCompatible B μ₂ μB νB →
      IsCompatible (A.prod B) (μ₁.prod μ₂) (productSubgroupMeasure A B μA μB)
        (productQuotientMeasure A B νA νB)

theorem productQuotientCompatibility : ProductQuotientCompatibilityStatement.{u₁, u₂} := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B hA hB
    _ _ _ _ _ _ μ₁ μ₂ _ _ μA μB _ _ _ _ _ _ νA νB hcA hcB
  exact productQuotientMeasure_isCompatible A B μA μB hA hB μ₁ μ₂ νA νB hcA hcB

end Langlands.QuotientIntegration
