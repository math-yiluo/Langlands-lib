import Langlands.Analysis.Local.LeftQuotientProduct
import Langlands.Analysis.Local.QuotientCompatibleScaling
import Langlands.BaseChange.RegularTransferMeasures
import Langlands.TraceFormula.ProductTwistedOrbitalStatement
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Metrizable.Urysohn

/-! # Twisted orbital integrals over a finite family of groups -/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory Topology
open Langlands.QuotientIntegration
open scoped CompactlySupported

universe u w

section CompactTests

variable {ι : Type w} [Fintype ι] {X : ι → Type u} [∀ i, TopologicalSpace (X i)]

/-- The product of compactly supported coordinate tests is supported in the product
of their supports. -/
private def compactPiProduct (f : ∀ i, C_c(X i, ℝ)) : C_c((∀ i, X i), ℝ) where
  toFun x := ∏ i, f i (x i)
  continuous_toFun := continuous_finsetProd _ fun i _ => (f i).continuous.comp (continuous_apply i)
  hasCompactSupport' := by
    classical
    refine HasCompactSupport.intro' (isCompact_univ_pi fun i => (f i).hasCompactSupport)
      (isClosed_set_pi fun i _ => isClosed_tsupport (f i)) ?_
    intro x hx
    obtain ⟨i, hi⟩ : ∃ i, x i ∉ tsupport (f i) := by simpa [Set.mem_pi] using hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)

variable [∀ i, T2Space (X i)] [∀ i, LocallyCompactSpace (X i)]
  [∀ i, SecondCountableTopology (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)]

/-- Equal integrals of compact product tests bound the regular measure of each open
rectangle by the other measure of that rectangle. -/
private theorem measure_openPi_le_of_tensor_integrals_eq
    (ρ τ : Measure (∀ i, X i)) [ρ.Regular]
    (htensor : ∀ f : ∀ i, C_c(X i, ℝ),
      (∫ x, compactPiProduct f x ∂ρ) = ∫ x, compactPiProduct f x ∂τ)
    (U : ∀ i, Set (X i)) (hU : ∀ i, IsOpen (U i)) :
    ρ (Set.pi Set.univ U) ≤ τ (Set.pi Set.univ U) := by
  classical
  have hopen : IsOpen (Set.pi Set.univ U) := isOpen_set_pi Set.finite_univ fun i _ => hU i
  rw [hopen.measure_eq_iSup_isCompact ρ]
  refine iSup_le fun K => iSup_le fun hKU => iSup_le fun hK => ?_
  have hproj (i : ι) : (fun x : (∀ i, X i) => x i) '' K ⊆ U i := by
    rintro _ ⟨x, hx, rfl⟩
    exact hKU hx i (Set.mem_univ i)
  choose f hone hzero hcompact hbound using fun i =>
    exists_continuous_one_zero_of_isCompact (hK.image (continuous_apply i))
      (hU i).isClosed_compl (Set.disjoint_compl_right_iff_subset.mpr (hproj i))
  let φ (i : ι) : C_c(X i, ℝ) := ⟨f i, hcompact i⟩
  let F := compactPiProduct φ
  have hnonneg (x : ∀ i, X i) : 0 ≤ F x := Finset.prod_nonneg fun i _ => (hbound i (x i)).1
  have hle (x : ∀ i, X i) : F x ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => (hbound i (x i)).1) (fun i _ => (hbound i (x i)).2)
  have hFone (x : ∀ i, X i) (hx : x ∈ K) : F x = 1 :=
    Finset.prod_eq_one fun i _ => hone i ⟨x, hx, rfl⟩
  have hFzero (x : ∀ i, X i) (hx : x ∈ (Set.pi Set.univ U)ᶜ) : F x = 0 := by
    obtain ⟨i, hi⟩ : ∃ i, x i ∉ U i := by simpa [Set.mem_pi] using hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hzero i hi)
  calc
    ρ K ≤ ENNReal.ofReal (∫ x, F x ∂ρ) :=
      (F.continuous.integrable_of_hasCompactSupport F.hasCompactSupport).measure_le_integral
        (ae_of_all _ hnonneg) (fun x hx => (hFone x hx).ge)
    _ = ENNReal.ofReal (∫ x, F x ∂τ) := congrArg ENNReal.ofReal (htensor φ)
    _ ≤ τ (Set.pi Set.univ U) := integral_le_measure (fun x _ => hle x) (fun x hx => (hFzero x hx).le)

private theorem eq_pi_of_tensor_integrals_eq
    (ν : ∀ i, Measure (X i)) [∀ i, (ν i).Regular] (ρ : Measure (∀ i, X i)) [ρ.Regular]
    (htensor : ∀ f : ∀ i, C_c(X i, ℝ),
      (∫ x, compactPiProduct f x ∂ρ) = ∫ x, compactPiProduct f x ∂Measure.pi ν) :
    ρ = Measure.pi ν := by
  let : ∀ i, SigmaFinite (ν i) := fun i => inferInstance
  let : (Measure.pi ν).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  symm
  refine Measure.pi_eq_generateFrom (C := fun i => {s : Set (X i) | IsOpen s})
    (fun i => (BorelSpace.measurable_eq (α := X i)).symm) (fun _ => isPiSystem_isOpen)
    (fun i => (ν i).finiteSpanningSetsInOpen) ?_
  intro U hU
  rw [← Measure.pi_pi ν U]
  exact le_antisymm (measure_openPi_le_of_tensor_integrals_eq ρ (Measure.pi ν) htensor U hU)
    (measure_openPi_le_of_tensor_integrals_eq (Measure.pi ν) ρ (fun f => (htensor f).symm) U hU)

end CompactTests

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
/-- The twisted orbit function of a finite tensor is integrable and its integral factors. -/
theorem piTwistedOrbitalIntegral : PiTwistedOrbitalIntegralStatement.{u, w} := by
  classical
  intro ι _ G _ _ _ _ _ _ _ _ μ _ θ' θ hθ' hθ δ _ _ _ _
    μC' _ _ _ μC _ _ _ ν' ν hc' hc hnormalize f _ hf
  let C' (i : ι) := twistedCentralizer (θ' i) (δ i)
  let C := twistedCentralizer θ δ
  have hθpi : Continuous θ := continuous_pi fun i => by
    simp only [hθ]
    exact (hθ' i).comp (continuous_apply i)
  have hC' (i : ι) : IsClosed (C' i : Set (G i)) := isClosed_twistedCentralizer (θ' i) (hθ' i) (δ i)
  have hC : IsClosed (C : Set (∀ i, G i)) := isClosed_twistedCentralizer θ hθpi δ
  have hCpi : C = Subgroup.pi Set.univ C' := by
    ext x
    simp only [C, C', Subgroup.mem_pi, mem_twistedCentralizer, Set.mem_univ, true_implies,
      funext_iff, Pi.mul_apply, Pi.inv_apply, hθ]
  let eC : LeftQuotient C ≃ₜ LeftQuotient (Subgroup.pi Set.univ C') :=
    Homeomorph.Quotient.congr (Homeomorph.refl _) (by
      intro x y
      change QuotientGroup.rightRel C x y ↔ QuotientGroup.rightRel (Subgroup.pi Set.univ C') x y
      rw [hCpi])
  let e := eC.trans (leftQuotientPiHomeomorph C')
  have he (x : ∀ i, G i) : e (Quotient.mk _ x) =
      fun i => (Quotient.mk _ (x i) : LeftQuotient (C' i)) := rfl
  let : ∀ i, LocallyCompactSpace (C' i) := fun i => (hC' i).locallyCompactSpace
  let : ∀ i, SecondCountableTopology (C' i) := fun _ => IsEmbedding.subtypeVal.secondCountableTopology
  let : ∀ i, SigmaFinite (μC' i) := fun i => inferInstance
  let : ∀ i, SigmaFinite ((μC' i).map (Subtype.val : C' i → G i)) := fun i =>
    (hC' i).isClosedEmbedding_subtypeVal.measurableEmbedding.sigmaFinite_map
  let : ∀ i, T2Space (LeftQuotient (C' i)) := fun i => leftQuotient_t2Space (C' i) (hC' i)
  let : ∀ i, LocallyCompactSpace (LeftQuotient (C' i)) := fun i =>
    leftQuotient_locallyCompactSpace (C' i)
  let : ∀ i, SecondCountableTopology (LeftQuotient (C' i)) := fun i =>
    (leftQuotient_isOpenQuotientMap (C' i)).secondCountableTopology
  let : ∀ i, (ν' i).Regular := fun i => (hc' i).regular
  let : ∀ i, SigmaFinite (ν' i) := fun i => inferInstance
  let : ∀ i, SigmaFinite (μ i) := fun i => inferInstance
  let : ν.Regular := hc.regular
  let : (ν.map e).Regular := Measure.Regular.map e
  have hν : ν.map e = Measure.pi ν' := by
    apply eq_pi_of_tensor_integrals_eq
    intro φ
    choose g hg _hpos using fun i =>
      exists_positiveLifting_of_isMulRightInvariant (C' i) (hC' i) (μC' i) (φ i)
    have havg (q : LeftQuotient C) :
        quotientAverageReal C μC (compactPiProduct g) q = compactPiProduct φ (e q) := by
      induction q using Quotient.inductionOn with
      | h x =>
        rw [quotientAverageReal_mk, he]
        change (∫ c : C, ∏ i, g i (c.val i * x i) ∂μC) = ∏ i, φ i (Quotient.mk _ (x i))
        calc
          _ = ∫ a : (∀ i, G i), ∏ i, g i (a i * x i) ∂μC.map Subtype.val := by
            symm
            exact hC.isClosedEmbedding_subtypeVal.integral_map _
          _ = ∏ i, ∫ a : G i, g i (a * x i) ∂(μC' i).map Subtype.val := by
            rw [hnormalize]
            exact integral_fintype_prod_eq_prod (fun i a => g i (a * x i))
          _ = _ := Finset.prod_congr rfl fun i _ =>
            ((hC' i).isClosedEmbedding_subtypeVal.integral_map (fun a => g i (a * x i))).trans
              (hg i (x i))
    calc
      _ = ∫ q, compactPiProduct φ (e q) ∂ν := integral_map_equiv e.toMeasurableEquiv _
      _ = ∫ q, quotientAverageReal C μC (compactPiProduct g) q ∂ν :=
        integral_congr_ae (ae_of_all _ fun q => (havg q).symm)
      _ = ∫ x, compactPiProduct g x ∂Measure.pi μ :=
        hc.integral_quotientAverageReal _ (compactPiProduct g).continuous
          (compactPiProduct g).hasCompactSupport
      _ = ∏ i, ∫ x, g i x ∂μ i := integral_fintype_prod_eq_prod (fun i => g i)
      _ = ∏ i, ∫ q, φ i q ∂ν' i := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← (hc' i).integral_quotientAverageReal
          (g i : G i → ℝ) (g i).continuous (g i).hasCompactSupport]
        apply integral_congr_ae
        refine ae_of_all _ fun q => ?_
        induction q using Quotient.inductionOn with
        | h x => exact hg i x
      _ = _ := (integral_fintype_prod_eq_prod (fun i => φ i)).symm
  let chart := e.toMeasurableEquiv
  have hpres : MeasurePreserving chart ν (Measure.pi ν') := ⟨chart.measurable, hν⟩
  let orbit (i : ι) := twistedOrbitFunction (θ' i) (δ i) (f i)
  have horbit : twistedOrbitFunction θ δ (fun x => ∏ i, f i (x i)) =
      (fun p => ∏ i, orbit i (p i)) ∘ chart := by
    funext q
    induction q using Quotient.inductionOn with
    | h x =>
      change twistedOrbitFunction θ δ (fun y => ∏ i, f i (y i)) (Quotient.mk _ x) =
        ∏ i, orbit i (e (Quotient.mk _ x) i)
      simp only [orbit, twistedOrbitFunction_mk, he, Pi.mul_apply, Pi.inv_apply, hθ]
      rfl
  constructor
  · rw [horbit]
    exact (hpres.integrable_comp_emb chart.measurableEmbedding).2 (Integrable.fintype_prod_dep hf)
  · change (∫ q, twistedOrbitFunction θ δ (fun x => ∏ i, f i (x i)) q ∂ν) =
      ∏ i, ∫ q, orbit i q ∂ν' i
    rw [horbit]
    calc
      _ = ∫ p, (∏ i, orbit i (p i)) ∂Measure.pi ν' := hpres.integral_comp chart.measurableEmbedding _
      _ = _ := integral_fintype_prod_eq_prod orbit

end Langlands.TraceFormula
