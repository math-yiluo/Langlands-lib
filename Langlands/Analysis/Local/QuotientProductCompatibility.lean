import Langlands.Analysis.Local.LeftQuotientProduct
import Langlands.Analysis.Local.QuotientAutomorphismProof
import Langlands.Analysis.Local.QuotientMeasureExistence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Metrizable.Urysohn

/-! Compatibility of product Haar and product left quotient measures. -/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure Topology
open scoped CompactlySupported

universe u v

variable {G₁ : Type u} {G₂ : Type v} [Group G₁] [Group G₂]
  [TopologicalSpace G₁] [TopologicalSpace G₂] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
  [MeasurableSpace G₁] [MeasurableSpace G₂] [BorelSpace G₁] [BorelSpace G₂]
  [SecondCountableTopology G₁] [SecondCountableTopology G₂]
  (A : Subgroup G₁) (B : Subgroup G₂)

local instance prodCompatibilitySubgroupSecondCountable {G : Type*} [Group G]
    [TopologicalSpace G] [SecondCountableTopology G] (H : Subgroup G) :
    SecondCountableTopology H :=
  IsEmbedding.subtypeVal.secondCountableTopology

/-- The product measure transported to the actual product subgroup. -/
def prodSubgroupMeasure (μA : Measure A) (μB : Measure B) : Measure (A.prod B) :=
  Measure.map (prodSubgroupHomeomorph A B).symm (μA.prod μB)

instance prodSubgroupMeasure_isHaar (μA : Measure A) (μB : Measure B)
    [μA.IsHaarMeasure] [μB.IsHaarMeasure] [SigmaFinite μA] [SigmaFinite μB] :
    (prodSubgroupMeasure A B μA μB).IsHaarMeasure :=
  (prodSubgroupHomeomorph A B).symm.isHaarMeasure_map (μA.prod μB)

instance prodSubgroupMeasure_rightInvariant (μA : Measure A) (μB : Measure B)
    [μA.IsMulRightInvariant] [μB.IsMulRightInvariant] [SigmaFinite μA] [SigmaFinite μB] :
    (prodSubgroupMeasure A B μA μB).IsMulRightInvariant :=
  isMulRightInvariant_map (prodSubgroupHomeomorph A B).symm (μA.prod μB)

omit [SecondCountableTopology G₁] in
private theorem quotientAverageReal_prod_mul
    (μA : Measure A) (μB : Measure B)
    [μA.IsMulRightInvariant] [μB.IsMulRightInvariant] [SigmaFinite μA] [SigmaFinite μB]
    (f₁ : G₁ → ℝ) (f₂ : G₂ → ℝ) (q : LeftQuotient (A.prod B)) :
    quotientAverageReal (A.prod B) (prodSubgroupMeasure A B μA μB)
        (fun x => f₁ x.1 * f₂ x.2) q =
      quotientAverageReal A μA f₁ (leftQuotientProdHomeomorph A B q).1 *
        quotientAverageReal B μB f₂ (leftQuotientProdHomeomorph A B q).2 := by
  induction q using Quotient.inductionOn with
  | h x =>
    simp only [leftQuotientProdHomeomorph_mk, quotientAverageReal_mk]
    calc
      (∫ k : A.prod B, f₁ (k.val * x).1 * f₂ (k.val * x).2
          ∂prodSubgroupMeasure A B μA μB) =
          ∫ k : A × B, f₁ (k.1.val * x.1) * f₂ (k.2.val * x.2) ∂μA.prod μB :=
        integral_map_equiv (prodSubgroupHomeomorph A B).symm.toHomeomorph.toMeasurableEquiv _
      _ = _ := integral_prod_mul (μ := μA) (ν := μB)
        (fun k : A => f₁ (k.val * x.1)) (fun k : B => f₂ (k.val * x.2))

variable [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]
  [MeasurableSpace (LeftQuotient B)] [BorelSpace (LeftQuotient B)]
  [MeasurableSpace (LeftQuotient (A.prod B))] [BorelSpace (LeftQuotient (A.prod B))]

/-- The product of the two left quotient measures on the actual product quotient. -/
def prodQuotientMeasure (νA : Measure (LeftQuotient A)) (νB : Measure (LeftQuotient B)) :
    Measure (LeftQuotient (A.prod B)) :=
  Measure.map (leftQuotientProdHomeomorph A B).symm (νA.prod νB)

private def compactFunctionProd (f₁ : C_c(G₁, ℝ)) (f₂ : C_c(G₂, ℝ)) : C_c(G₁ × G₂, ℝ) where
  toFun x := f₁ x.1 * f₂ x.2
  continuous_toFun := (f₁.continuous.comp continuous_fst).mul
    (f₂.continuous.comp continuous_snd)
  hasCompactSupport' := by
    apply (f₁.hasCompactSupport.prod f₂.hasCompactSupport).of_isClosed_subset
      (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport _ |>.prod (isClosed_tsupport _))
    intro x hx
    have hx' : f₁ x.1 * f₂ x.2 ≠ 0 := hx
    exact ⟨subset_tsupport _ (left_ne_zero_of_mul hx'), subset_tsupport _ (right_ne_zero_of_mul hx')⟩

set_option maxHeartbeats 1000000 in
/-- Product ambient and subgroup Haar measures give the product of compatible
quotient measures, with its exact product normalization. -/
theorem prodQuotientMeasure_isCompatible
    [T2Space G₁] [T2Space G₂] [LocallyCompactSpace G₁] [LocallyCompactSpace G₂]
    (hA : IsClosed (A : Set G₁)) (hB : IsClosed (B : Set G₂))
    (μ₁ : Measure G₁) (μ₂ : Measure G₂) [μ₁.IsHaarMeasure] [μ₂.IsHaarMeasure]
    [μ₁.IsMulRightInvariant] [μ₂.IsMulRightInvariant]
    (μA : Measure A) (μB : Measure B) [μA.IsHaarMeasure] [μB.IsHaarMeasure]
    [μA.IsMulRightInvariant] [μB.IsMulRightInvariant] [SigmaFinite μA] [SigmaFinite μB]
    (νA : Measure (LeftQuotient A)) (νB : Measure (LeftQuotient B))
    (hνA : IsCompatible A μ₁ μA νA) (hνB : IsCompatible B μ₂ μB νB) :
    IsCompatible (A.prod B) (μ₁.prod μ₂) (prodSubgroupMeasure A B μA μB)
      (prodQuotientMeasure A B νA νB) := by
  let : LocallyCompactSpace (LeftQuotient A) := leftQuotient_locallyCompactSpace A
  let : LocallyCompactSpace (LeftQuotient B) := leftQuotient_locallyCompactSpace B
  let : T2Space (LeftQuotient A) := leftQuotient_t2Space A hA
  let : T2Space (LeftQuotient B) := leftQuotient_t2Space B hB
  let : SecondCountableTopology (LeftQuotient A) :=
    IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap A)
  let : SecondCountableTopology (LeftQuotient B) :=
    IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap B)
  let : νA.Regular := hνA.regular
  let : νB.Regular := hνB.regular
  let : (νA.prod νB).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (νA.prod νB)
  let e := leftQuotientProdHomeomorph A B
  let ν₀ := prodQuotientMeasure A B νA νB
  let : ν₀.Regular := Measure.Regular.map e.symm
  have hNe : ν₀ ≠ 0 := by
    apply (Measure.map_ne_zero_iff e.symm.continuous.measurable.aemeasurable).2
    intro hz
    have he : νA Set.univ * νB Set.univ = 0 := by
      rw [← Measure.prod_prod, hz]
      simp
    exact mul_ne_zero (fun h => hνA.nonzero (Measure.measure_univ_eq_zero.mp h))
      (fun h => hνB.nonzero (Measure.measure_univ_eq_zero.mp h)) he
  have hInvariant (g : G₁ × G₂) : MeasurePreserving (rightTranslate (A.prod B) g) ν₀ ν₀ :=
    measurePreserving_map_symm_of_conj e.toMeasurableEquiv (νA.prod νB)
      (rightTranslate (A.prod B) g).continuous.measurable
      (leftQuotientProdHomeomorph_rightTranslate A B g)
      ((hνA.right_invariant g.1).prod (hνB.right_invariant g.2))
  have hClosed : IsClosed (A.prod B : Set (G₁ × G₂)) := hA.prod hB
  let μH := prodSubgroupMeasure A B μA μB
  let : LocallyCompactSpace (A.prod B) := hClosed.locallyCompactSpace
  let : TopologicalSpace.PseudoMetrizableSpace (A.prod B) :=
    IsInducing.subtypeVal.pseudoMetrizableSpace
  let : (μ₁.prod μ₂).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (μ₁.prod μ₂)
  let : μH.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μH
  obtain ⟨ν, hν⟩ := compatibleMeasureExists (A.prod B) hClosed (μ₁.prod μ₂) μH
  let : ν.Regular := hν.regular
  obtain ⟨c, hc, heq⟩ := exists_pos_smul_eq_of_rightInvariant_quotient
    (A.prod B) hClosed μH ν ν₀ hν.nonzero hNe hν.right_invariant hInvariant
  obtain ⟨f₁, hf₁⟩ := exists_compact_integral_ne_zero μ₁ (NeZero.ne μ₁)
  obtain ⟨f₂, hf₂⟩ := exists_compact_integral_ne_zero μ₂ (NeZero.ne μ₂)
  let f := compactFunctionProd f₁ f₂
  have hIntegral : (∫ q, quotientAverageReal (A.prod B) μH f q ∂ν₀) =
      (∫ x, f₁ x ∂μ₁) * (∫ y, f₂ y ∂μ₂) := by
    calc
      _ = ∫ q, quotientAverageReal (A.prod B) μH f (e.symm q) ∂νA.prod νB :=
        integral_map_equiv e.symm.toMeasurableEquiv _
      _ = ∫ q, quotientAverageReal A μA f₁ q.1 * quotientAverageReal B μB f₂ q.2 ∂νA.prod νB := by
        apply integral_congr_ae
        refine ae_of_all _ fun q => ?_
        have he := quotientAverageReal_prod_mul A B μA μB f₁ f₂ (e.symm q)
        change _ = quotientAverageReal A μA f₁ (e (e.symm q)).1 *
          quotientAverageReal B μB f₂ (e (e.symm q)).2 at he
        rwa [e.apply_symm_apply] at he
      _ = _ := by
        rw [integral_prod_mul, hνA.integral_quotientAverageReal f₁ f₁.continuous f₁.hasCompactSupport,
          hνB.integral_quotientAverageReal f₂ f₂.continuous f₂.hasCompactSupport]
  have hCompare := hν.integral_quotientAverageReal f f.continuous f.hasCompactSupport
  rw [heq, integral_smul_measure, ENNReal.toReal_ofReal hc.le, hIntegral] at hCompare
  change c * ((∫ x, f₁ x ∂μ₁) * (∫ y, f₂ y ∂μ₂)) =
    (∫ x : G₁ × G₂, f₁ x.1 * f₂ x.2 ∂μ₁.prod μ₂) at hCompare
  rw [integral_prod_mul] at hCompare
  have hc₁ : c = 1 := mul_right_cancel₀ (mul_ne_zero hf₁ hf₂) (by simpa using hCompare)
  rw [hc₁, ENNReal.ofReal_one, one_smul] at heq
  change IsCompatible (A.prod B) (μ₁.prod μ₂) μH ν₀
  rwa [← heq]

end Langlands.QuotientIntegration
