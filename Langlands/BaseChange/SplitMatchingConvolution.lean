import Langlands.BaseChange.SplitMatchingChart
import Mathlib.MeasureTheory.Integral.Prod

/-! Integration on the fibers of ordered multiplication for the split matching proof. -/

noncomputable section

open MeasureTheory Topology
open scoped BigOperators

namespace Langlands.BaseChange

open HarmonicAnalysis (SchwartzBruhat)

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem continuous_splitOrderedProduct {l : ℕ} :
    Continuous (fun x : Fin l → G => (List.ofFn x).prod) := by
  induction l with
  | zero => simpa only [List.ofFn_zero, List.prod_nil] using continuous_const (y := (1 : G))
  | succ l ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact (continuous_apply 0).mul (ih.comp (continuous_pi fun i => continuous_apply i.succ))

/-- Use the total ordered product and the first `l` entries as coordinates. -/
def splitProductFiberChart (l : ℕ) : G × (Fin l → G) ≃ₜ (Fin (l + 1) → G) where
  toFun p := Fin.snoc p.2 ((List.ofFn p.2).prod⁻¹ * p.1)
  invFun x := ((List.ofFn x).prod, Fin.init x)
  left_inv p := by
    apply Prod.ext
    · change (List.ofFn (Fin.snoc p.2 ((List.ofFn p.2).prod⁻¹ * p.1))).prod = p.1
      rw [splitOrderedProduct_snoc, mul_inv_cancel_left]
    · exact Fin.init_snoc (α := fun _ => G) _ _
  right_inv x := by
    change Fin.snoc (Fin.init x) ((List.ofFn (Fin.init x)).prod⁻¹ * (List.ofFn x).prod) = x
    rw [splitOrderedProduct_init_last x, inv_mul_cancel_left, Fin.snoc_init_self]
  continuous_toFun := continuous_pi fun i => by
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      exact (continuous_splitOrderedProduct.comp continuous_snd).inv.mul continuous_fst
    | cast i =>
      simp only [Fin.snoc_castSucc]
      exact (continuous_apply i).comp continuous_snd
  continuous_invFun := continuous_splitOrderedProduct.prodMk
    (continuous_pi fun i => continuous_apply i.castSucc)

theorem splitProductFiberChart_apply {l : ℕ} (g : G) (w : Fin l → G) :
    splitProductFiberChart l (g, w) = Fin.snoc w ((List.ofFn w).prod⁻¹ * g) := rfl

private theorem splitProductFiberChart_cons {l : ℕ} (g x : G) (w : Fin l → G) :
    splitProductFiberChart (l + 1) (g, Fin.cons x w) =
      Fin.cons x (splitProductFiberChart l (x⁻¹ * g, w)) := by
  rw [splitProductFiberChart_apply, splitProductFiberChart_apply, Fin.cons_snoc_eq_snoc_cons,
    List.ofFn_succ]
  simp [mul_inv_rev, mul_assoc]

omit [Group G] [IsTopologicalGroup G] in
private theorem splitCoordinateTensor_hasCompactSupport {l : ℕ}
    (ψ : Fin (l + 1) → SchwartzBruhat G) :
    HasCompactSupport (fun x : Fin (l + 1) → G => ∏ i, ψ i (x i)) := by
  refine (isCompact_univ_pi fun i => (ψ i).hasCompactSupport).of_isClosed_subset
    isClosed_closure (closure_minimal ?_ (isClosed_set_pi fun i _ => isClosed_tsupport (ψ i)))
  intro x hx i _
  apply subset_tsupport (ψ i)
  exact fun h => hx (Finset.prod_eq_zero (Finset.mem_univ i) h)

/-- Pulling the coordinate tensor back along a closed embedding gives an integrable function. -/
theorem splitProductFiber_integrable {l : ℕ} {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {j : X → G × (Fin l → G)} (hj : IsClosedEmbedding j)
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (ψ : Fin (l + 1) → SchwartzBruhat G) :
    Integrable (fun x => ∏ i, ψ i (splitProductFiberChart l (j x) i)) ν := by
  have he := (splitProductFiberChart l).isClosedEmbedding.comp hj
  have hc : Continuous (fun x : Fin (l + 1) → G => ∏ i, ψ i (x i)) :=
    continuous_finsetProd _ fun i _ => (ψ i).continuous.comp (continuous_apply i)
  exact (hc.comp he.continuous).integrable_of_hasCompactSupport
    ((splitCoordinateTensor_hasCompactSupport ψ).comp_isClosedEmbedding he)

/-- Integrate the split tensor over the free entries at a fixed ordered product. -/
theorem integral_splitProductFiber [MeasurableSpace G] [BorelSpace G]
    [T2Space G] [SecondCountableTopology G] (μ : Measure G)
    [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ] {l : ℕ}
    (ψ : Fin (l + 1) → SchwartzBruhat G) (g : G) :
    (∫ w, ∏ i, ψ i (splitProductFiberChart l (g, w) i) ∂Measure.pi (fun _ : Fin l => μ)) =
      convolutionProduct μ ψ g := by
  induction l generalizing g with
  | zero =>
    rw [Measure.pi_of_empty _ (Fin.elim0 : Fin 0 → G), integral_dirac, convolutionProduct_zero]
    simp [splitProductFiberChart_apply, Fin.snoc_zero]
  | succ l ih =>
    let f (w : Fin (l + 1) → G) := ∏ i, ψ i (splitProductFiberChart (l + 1) (g, w) i)
    let e := (splitFinHead (G := G) l).toMeasurableEquiv
    have hj : IsClosedEmbedding (Prod.mk g : (Fin (l + 1) → G) → _) := by
      refine ⟨isEmbedding_prodMkRight g, ?_⟩
      rw [show Set.range (Prod.mk g : (Fin (l + 1) → G) → _) = Prod.fst ⁻¹' {g} by
        ext p
        rcases p with ⟨x, w⟩
        simp [eq_comm]]
      exact isClosed_singleton.preimage continuous_fst
    have hf : Integrable f (Measure.pi fun _ : Fin (l + 1) => μ) :=
      splitProductFiber_integrable hj _ ψ
    have hm := (splitFinHead_measurePreserving μ l).symm e
    change (∫ w, f w ∂Measure.pi (fun _ : Fin (l + 1) => μ)) = _
    calc
      _ = ∫ p, f (e.symm p) ∂μ.prod (Measure.pi fun _ : Fin l => μ) :=
        (hm.integral_comp e.symm.measurableEmbedding f).symm
      _ = ∫ x, ∫ w, f (Fin.cons x w) ∂Measure.pi (fun _ : Fin l => μ) ∂μ :=
        integral_prod _ (hm.integrable_comp_emb e.symm.measurableEmbedding |>.mpr hf)
      _ = convolutionProduct μ ψ g := by
        rw [convolutionProduct_succ, Hecke.TestFunction.convolution_apply]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          have hsplit (w : Fin l → G) :
              f (Fin.cons x w) =
                ψ 0 x * ∏ i, Fin.tail ψ i (splitProductFiberChart l (x⁻¹ * g, w) i) := by
            dsimp only [f]
            rw [splitProductFiberChart_cons, Fin.prod_univ_succ]
            simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]
          simp_rw [hsplit]
          rw [integral_const_mul, ih (Fin.tail ψ) (x⁻¹ * g)]

end Langlands.BaseChange
