import Langlands.Geometry.Manifold.LieGroupEllipticEstimateProof
import Langlands.Analysis.CompactFunctionalFactorization
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Geometry.Manifold.BumpFunction

/-! # Compact bounds on the translated curves of elliptic solutions -/

noncomputable section

open MeasureTheory Set Filter Metric TopologicalSpace
open scoped Manifold ContDiff Topology Pointwise ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.Geometry.Manifold

open Langlands.Analysis Langlands.Analysis.CompactFunctional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [ChartedSpace E H] [LieGroup 𝓘(ℝ, E) ∞ H]

local notation "𝓘E" => 𝓘(ℝ, E)
local notation "F" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [IsTopologicalGroup H] [T2Space H] in
/-- Every jet at the identity is bounded by a multiple of one compact supremum norm. -/
private theorem exists_chartJet_bound {n r : ℕ} (hr : 0 < r)
    (X : Fin n → GroupLieAlgebra 𝓘E H) (Ptop Plow : MonoidAlgebra ℂ (FreeMonoid (Fin n)))
    (htop : ∀ w ∈ Ptop.coeff.support, w.length = r)
    (hlow : ∀ w ∈ Plow.coeff.support, w.length < r)
    (hell : ∀ ξ : GroupLieAlgebra 𝓘E H →ₗ[ℝ] ℝ, ξ ≠ 0 → lieWordSymbol X ξ Ptop ≠ 0) :
    let L : E ≃L[ℝ] F := toEuclidean
    let e := extChartAt 𝓘E (1 : H)
    let ψ := e.symm ∘ L.symm
    let x₀ := L (e 1)
    ∃ (V : Compacts H) (C : ℕ → ℝ), (∀ m, 0 ≤ C m) ∧
      ∀ f : C(H, ℂ), ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ f →
        (∀ x, lieWordAction X (Ptop + Plow) f x = 0) →
        ∀ m, ‖iteratedFDeriv ℝ m (f ∘ ψ) x₀‖ ≤ C m * ‖CompactFunctional.restrict V f‖ := by
  let L : E ≃L[ℝ] F := toEuclidean
  let e := extChartAt 𝓘E (1 : H)
  let T := L.symm ⁻¹' e.target
  let ψ := e.symm ∘ L.symm
  let x₀ := L (e 1)
  obtain ⟨D, _, hTo, hx₀, _, hψ, hD, hcoef, hellD, haction, _⟩ :=
    exists_lieWordCoordinateOperator X Ptop Plow htop hlow hell
  obtain ⟨R, _, hRT, C, hC, hest⟩ :=
    exists_localElliptic_interior_derivative_l2_bounds hr D hD hTo hcoef hx₀ hellD
  let V : Compacts H := ⟨ψ '' closedBall x₀ R,
    (isCompact_closedBall _ _).image_of_continuousOn (hψ.continuousOn.mono hRT)⟩
  let M := (volume (closedBall x₀ R) : ℝ≥0∞) ^ (1 / 2 : ℝ)
  have hM : M ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_closedBall_lt_top.ne
  refine ⟨V, fun m => (C m).toReal * M.toReal, fun _ => by positivity, ?_⟩
  intro f hf hsol m
  have hchart : ContDiffOn ℝ ∞ (f ∘ ψ) T :=
    contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn hψ)
  have hj := hest (f ∘ ψ) hchart (fun x hx => (haction f hf x hx).trans (hsol _)) m
  have hlp := eLpNorm_le_of_ae_bound (p := 2) (μ := volume.restrict (closedBall x₀ R))
    (hchart.continuousOn.mono hRT |>.aestronglyMeasurable measurableSet_closedBall)
    (ae_restrict_of_forall_mem measurableSet_closedBall fun x hx =>
      (CompactFunctional.restrict V f).norm_coe_le_norm ⟨ψ x, mem_image_of_mem ψ hx⟩)
  rw [Measure.restrict_apply_univ, show (2 : ℝ≥0∞).toReal⁻¹ = (1 / 2 : ℝ) by norm_num] at hlp
  have hk := hj.trans (mul_le_mul' le_rfl hlp)
  have hfin : C m * (M * ENNReal.ofReal ‖CompactFunctional.restrict V f‖) ≠ ⊤ :=
    ENNReal.mul_ne_top (hC m) (ENNReal.mul_ne_top hM ENNReal.ofReal_ne_top)
  have hz := ENNReal.toReal_mono hfin hk
  rwa [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _),
    ← mul_assoc] at hz

/-- One compact domain bounds all derivatives of a translated elliptic solution along a smooth
one-parameter subgroup, uniformly on the starting compact and parameter interval. -/
theorem lineDerivativeBounds_of_wordEquation {n r : ℕ} (hr : 0 < r)
    (X : Fin n → GroupLieAlgebra 𝓘E H) (Ptop Plow : MonoidAlgebra ℂ (FreeMonoid (Fin n)))
    (htop : ∀ w ∈ Ptop.coeff.support, w.length = r)
    (hlow : ∀ w ∈ Plow.coeff.support, w.length < r)
    (hell : ∀ ξ : GroupLieAlgebra 𝓘E H →ₗ[ℝ] ℝ, ξ ≠ 0 → lieWordSymbol X ξ Ptop ≠ 0)
    (S : Submodule ℂ C(H, ℂ))
    (hsol : ∀ f ∈ S, ContMDiff 𝓘E 𝓘(ℝ, ℂ) ∞ f ∧ ∀ x, lieWordAction X (Ptop + Plow) f x = 0)
    (hshift : ∀ a f, f ∈ S → shift a f ∈ S)
    (B : Compacts H) (q : ℝ → H) (hq : ContMDiff 𝓘(ℝ) 𝓘E ∞ q) (hq0 : q 0 = 1)
    (hqa : ∀ s t, q (s + t) = q s * q t) (ε : ℝ) : LineDerivativeBounds S B q ε := by
  classical
  let L : E ≃L[ℝ] F := toEuclidean
  let e := extChartAt 𝓘E (1 : H)
  let ψ := e.symm ∘ L.symm
  let T := L.symm ⁻¹' e.target
  let x₀ := L (e 1)
  have hTo : IsOpen T := (isOpen_extChartAt_target (I := 𝓘E) (1 : H)).preimage L.symm.continuous
  have hx₀ : x₀ ∈ T := by simpa only [T, x₀, mem_preimage, L.symm_apply_apply] using
    (mem_extChartAt_target (I := 𝓘E) (1 : H))
  have hψ : ContMDiffOn 𝓘(ℝ, F) 𝓘E ∞ ψ T :=
    (contMDiffOn_extChartAt_symm (I := 𝓘E) (1 : H)).comp L.symm.contDiff.contMDiff.contMDiffOn
      (fun _ h => h)
  obtain ⟨V, C, hC, hjet⟩ := exists_chartJet_bound hr X Ptop Plow htop hlow hell
  let W : Compacts H := ⟨((q '' Icc 0 ε) * (B : Set H)) * (V : Set H),
    ((isCompact_Icc.image hq.continuous).mul B.isCompact).mul V.isCompact⟩
  let β : SmoothBumpFunction 𝓘E (1 : H) := Classical.choice inferInstance
  let coord (a : H) := L (β a • e a)
  have hcoords : ContMDiff 𝓘E 𝓘(ℝ, F) ∞ coord := by
    apply L.contDiff.contMDiff.comp
    exact β.contMDiff_smul (fun x hx => (contMDiffAt_extChartAt' hx).contMDiffWithinAt)
  have hcoord : coord =ᶠ[𝓝 (1 : H)] (fun a => L (e a)) := by
    filter_upwards [β.eventuallyEq_one] with a ha
    change β a = (1 : ℝ) at ha
    simp only [coord, ha, one_smul]
  have hcoord₀ : coord 1 = x₀ := hcoord.eq_of_nhds
  let Q (p : ℝ × H) := coord (p.2⁻¹ * q p.1 * p.2)
  have hQ : ContMDiff (𝓘(ℝ).prod 𝓘E) 𝓘(ℝ, F) ∞ Q :=
    hcoords.comp ((contMDiff_snd.inv.mul (hq.comp contMDiff_fst)).mul contMDiff_snd)
  let j : C(B, H) := ⟨Subtype.val, continuous_subtype_val⟩
  let U (s : ℝ) : C(B, F) := ⟨fun y => Q (s, j y),
    hQ.continuous.comp (continuous_const.prodMk j.continuous)⟩
  have hU : ContDiff ℝ ∞ U := contMDiff_iff_contDiff.mp
    (contMDiff_compactFamily_of_joint j hQ (fun _ _ => rfl))
  let D (p : ℕ) := 1 + ∑ i ∈ Finset.range (p + 1), ‖iteratedDeriv i U 0‖
  let J (p : ℕ) := ∑ i ∈ Finset.range (p + 1), C i
  have hD (p : ℕ) : 1 ≤ D p := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hJ (p : ℕ) : 0 ≤ J p := Finset.sum_nonneg fun i _ => hC i
  have hbound_nonneg (p : ℕ) : 0 ≤ (p.factorial : ℝ) * J p * D p ^ p :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hJ p)) (pow_nonneg (zero_le_one.trans (hD p)) _)
  refine ⟨W, fun p => p.factorial * J p * D p ^ p, hbound_nonneg, ?_⟩
  intro f hf p t ht
  apply (ContinuousMap.norm_le _ (mul_nonneg (hbound_nonneg p) (norm_nonneg _))).2
  intro y
  let θ (s : ℝ) := Q (s, y.val)
  have hθ : ContDiff ℝ ∞ θ := contMDiff_iff_contDiff.mp (hQ.comp
    (contMDiff_id.prodMk contMDiff_const))
  have hθ0 : θ 0 = x₀ := by simpa [θ, Q, hq0] using hcoord₀
  let a := q t * y.val
  let fₐ := shift a f
  have hfₐ := (hsol fₐ (hshift a f hf)).1
  have hSolₐ := (hsol fₐ (hshift a f hf)).2
  have hnorm : ‖CompactFunctional.restrict V fₐ‖ ≤ ‖CompactFunctional.restrict W f‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro z
    have hz : a * z.val ∈ (W : Set H) :=
      mul_mem_mul (mul_mem_mul (mem_image_of_mem q ht) y.property) z.property
    exact (CompactFunctional.restrict W f).norm_coe_le_norm ⟨a * z.val, hz⟩
  let s := θ ⁻¹' T
  have hso : IsOpen s := hTo.preimage hθ.continuous
  have hs0 : (0 : ℝ) ∈ s := by simpa only [s, mem_preimage, hθ0] using hx₀
  have hF : ContDiffOn ℝ ∞ (fₐ ∘ ψ) T := contMDiffOn_iff_contDiffOn.mp (hfₐ.comp_contMDiffOn hψ)
  have hcomp := norm_iteratedFDerivWithin_comp_le hF (hθ.contDiffOn (s := s))
    (n := p) (x := 0) (by simp) hTo.uniqueDiffOn hso.uniqueDiffOn
    (show MapsTo θ s T from fun _ hx => hx) hs0 (C := J p * ‖CompactFunctional.restrict W f‖) (D := D p) (by
      intro i hi
      have hCi : C i ≤ J p := Finset.single_le_sum (fun j _ => hC j) (Finset.mem_range.mpr (by omega))
      rw [hθ0, iteratedFDerivWithin_of_isOpen i hTo hx₀]
      exact (hjet fₐ hfₐ hSolₐ i).trans (mul_le_mul hCi hnorm (norm_nonneg _) (hJ p))) (by
      intro i hi hip
      rw [iteratedFDerivWithin_of_isOpen i hso hs0, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have he : iteratedDeriv i θ 0 = iteratedDeriv i U 0 y :=
        iteratedDeriv_real_clm (ContinuousMap.evalCLM ℝ y) hU i 0
      rw [he]
      calc
        _ ≤ ‖iteratedDeriv i U 0‖ := (iteratedDeriv i U 0).norm_coe_le_norm y
        _ ≤ D p := (Finset.single_le_sum (fun j _ => norm_nonneg (iteratedDeriv j U 0))
          (Finset.mem_range.mpr (by omega))).trans (le_add_of_nonneg_left zero_le_one)
        _ ≤ D p ^ i := by
          simpa only [pow_one] using (pow_le_pow_right₀ (hD p) hi))
  rw [iteratedFDerivWithin_of_isOpen p hso hs0, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hcomp
  let qy (s : ℝ) := y.val⁻¹ * q s * y.val
  have hqy : Continuous qy := (continuous_const.mul hq.continuous).mul continuous_const
  have hqy0 : qy 0 = 1 := by simp [qy, hq0]
  have htend : Tendsto qy (𝓝 0) (𝓝 (1 : H)) := hqy.continuousAt.tendsto.trans_eq (by rw [hqy0])
  have hnear : ((fₐ ∘ ψ) ∘ θ) =ᶠ[𝓝 (0 : ℝ)] (fun s => f (q (s + t) * y.val)) := by
    filter_upwards [htend.eventually hcoord,
      htend.eventually ((isOpen_extChartAt_source (I := 𝓘E) (1 : H)).mem_nhds
        (mem_extChartAt_source (I := 𝓘E) (1 : H)))] with s hcs hqs
    change f (a * e.symm (L.symm (coord (qy s)))) = f (q (s + t) * y.val)
    rw [show coord (qy s) = L (e (qy s)) from hcs, L.symm_apply_apply, e.left_inv hqs,
      add_comm s t, hqa]
    congr 1
    dsimp only [a, qy]
    group
  let curve (s : ℝ) := f (q s * y.val)
  have htranslate := congrFun (iteratedDeriv_comp_add_const p curve t) 0
  change iteratedDeriv p (fun s => f (q (s + t) * y.val)) 0 = iteratedDeriv p curve (0 + t) at htranslate
  rw [zero_add] at htranslate
  rw [hnear.iteratedDeriv_eq, htranslate] at hcomp
  have hfcurve := contMDiff_restrict_mul (B := B) hq (hsol f hf).1
  have hev := iteratedDeriv_clm (ContinuousMap.evalCLM ℂ y) hfcurve p t
  change iteratedDeriv p curve t =
    (iteratedDeriv p (fun s => CompactFunctional.restrict B (shift (q s) f)) t) y at hev
  rw [← hev]
  refine hcomp.trans_eq ?_
  ac_rfl

end Langlands.Geometry.Manifold
