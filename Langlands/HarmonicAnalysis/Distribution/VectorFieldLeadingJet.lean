import Langlands.HarmonicAnalysis.Distribution.ProductJetTransform
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Logic.Equiv.Fin.Rotate

/-! # The action of a vector field on the first potentially nonzero jet -/

noncomputable section

open Filter Function Set
open scoped ContDiff Topology

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem iteratedFDeriv_slice {f : ℝ × E → F} (hf : ContDiff ℝ ∞ f)
    (k : ℕ) (t : ℝ) (x : E) (v : Fin k → E) :
    iteratedFDeriv ℝ k (fun y => f (t, y)) x v =
      iteratedFDeriv ℝ k f (t, x) (fun j => (0, v j)) := by
  let I := ContinuousLinearMap.inr ℝ ℝ E
  let g : ℝ × E → F := fun p => f ((t, 0) + p)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add contDiff_id)
  have h := I.iteratedFDeriv_comp_right hg x (i := k) (by simp)
  have hs : iteratedFDeriv ℝ k g (I x) = iteratedFDeriv ℝ k f (t, x) := by
    simpa only [g, I, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] using
      (iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := f) k ((t, 0) : ℝ × E) (I x))
  rw [hs] at h
  have hfun : (fun y => f (t, y)) = g ∘ I := by
    funext y
    simp [g, I]
  rw [hfun, h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

private theorem hasDerivAt_iteratedFDeriv_slice {f : ℝ × E → F} (hf : ContDiff ℝ ∞ f)
    (k : ℕ) (t : ℝ) (x : E) (v : Fin k → E) :
    HasDerivAt (fun s => iteratedFDeriv ℝ k (fun y => f (s, y)) x v)
      (iteratedFDeriv ℝ k (fun y => fderiv ℝ f (t, y) (1, 0)) x v) t := by
  let u : Fin k → ℝ × E := fun j => (0, v j)
  let d : ℝ × E := (1, 0)
  have hcurve : HasDerivAt (fun s : ℝ => (s, x)) d t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have hdiff := hf.differentiable_iteratedFDeriv
    (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)) (t, x)
  have hd := (hdiff.hasFDerivAt.continuousMultilinear_apply_const u).comp_hasDerivAt t hcurve
  have hD : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hE : ContDiff ℝ ∞ (fun p => fderiv ℝ f p d) := hD.clm_apply contDiff_const
  have hsymm : iteratedFDeriv ℝ (k + 1) f (t, x) (Fin.snoc u d) =
      iteratedFDeriv ℝ (k + 1) f (t, x) (Fin.cons d u) := by
    rw [Fin.snoc_eq_cons_rotate]
    exact Langlands.Analysis.iteratedFDeriv_comp_perm_of_contDiffAt hf.contDiffAt (by simp)
      (Fin.cons d u) (finRotate (k + 1))
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_succ_apply_left,
    Fin.init_snoc, Fin.snoc_last, Fin.cons_zero, Fin.tail_cons] at hsymm
  have hcoeff : iteratedFDeriv ℝ k (fun y => fderiv ℝ f (t, y) d) x v =
      (fderiv ℝ (iteratedFDeriv ℝ k f) (t, x) d) u := by
    rw [iteratedFDeriv_slice hE, iteratedFDeriv_clm_apply_const_apply hD (by simp)]
    exact hsymm
  rw [hcoeff]
  refine hd.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  exact iteratedFDeriv_slice hf k s x v

/-- Apply the same linear map to one slot of a continuous multilinear jet. -/
private def jetSlot {k : ℕ} (D : E →L[ℝ] E) (j : Fin k) :
    Module.End ℝ (E [×k]→L[ℝ] F) :=
  (ContinuousMultilinearMap.compContinuousLinearMapL
    (F := F) (Function.update (fun _ : Fin k => ContinuousLinearMap.id ℝ E) j D)).toLinearMap

private theorem jetSlot_apply {k : ℕ} (D : E →L[ℝ] E) (j : Fin k)
    (A : E [×k]→L[ℝ] F) (v : Fin k → E) :
    jetSlot D j A v = A (Function.update v j (D (v j))) := by
  change A (fun l => Function.update (fun _ : Fin k => ContinuousLinearMap.id ℝ E) j D l (v l)) = _
  congr 1
  funext l
  by_cases h : l = j
  · subst l
    simp
  · simp [Function.update_of_ne h]

/-- Sum the action of a linear map on the individual slots of a jet. -/
def jetSlotSum (k : ℕ) (D : E →L[ℝ] E) : Module.End ℝ (E [×k]→L[ℝ] F) :=
  ∑ j : Fin k, jetSlot D j

theorem jetSlotSum_apply (k : ℕ) (D : E →L[ℝ] E) (A : E [×k]→L[ℝ] F) (v : Fin k → E) :
    jetSlotSum k D A v = ∑ j : Fin k, A (Function.update v j (D (v j))) := by
  simp only [jetSlotSum, LinearMap.coe_sum, Finset.sum_apply, sum_apply, jetSlot_apply]

private theorem jetSlot_pow_apply {k : ℕ} (D : E →L[ℝ] E) (j : Fin k) (m : ℕ)
    (A : E [×k]→L[ℝ] F) (v : Fin k → E) :
    ((jetSlot D j ^ m) A) v = A (Function.update v j ((D.toLinearMap ^ m) (v j))) := by
  induction m generalizing v with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, jetSlot_apply, ih, Function.update_self,
      Function.update_idem, pow_succ, Module.End.mul_apply]
    rfl

private theorem commute_jetSlot {k : ℕ} (D : E →L[ℝ] E) (i j : Fin k) :
    Commute (jetSlot (F := F) D i) (jetSlot D j) := by
  by_cases hij : i = j
  · subst j
    exact Commute.refl _
  · apply LinearMap.ext
    intro A
    ext1 v
    simp only [Module.End.mul_apply, jetSlot_apply, Function.update_of_ne hij,
      Function.update_of_ne (Ne.symm hij)]
    rw [Function.update_comm (Ne.symm hij)]

/-- A common nilpotence exponent for the action on each jet of order `k`. -/
theorem jetSlotSum_pow_eq_zero (k : ℕ) (D : E →L[ℝ] E) (m : ℕ)
    (hm : D.toLinearMap ^ m = 0) :
    (jetSlotSum (F := F) k D) ^ (k * m + 1) = 0 := by
  have hslot (j : Fin k) : (jetSlot (F := F) D j) ^ m = 0 := by
    apply LinearMap.ext
    intro A
    ext1 v
    simp only [jetSlot_pow_apply, hm, LinearMap.zero_apply, zero_apply]
    exact A.map_coord_zero j (Function.update_self _ _ _)
  have hsum (s : Finset (Fin k)) :
      (∑ j ∈ s, jetSlot (F := F) D j) ^ (s.card * m + 1) = 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.card_insert_of_notMem hj]
      have hc : Commute (jetSlot (F := F) D j) (∑ i ∈ s, jetSlot D i) :=
        Commute.sum_right s _ _ (fun i _ => commute_jetSlot D j i)
      exact hc.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero (hslot j) ih (by rw [Nat.add_mul]; omega)
  simpa only [jetSlotSum, Finset.card_univ, Fintype.card_fin] using hsum Finset.univ

theorem jetSlotSum_finrank_pow_eq_zero [FiniteDimensional ℝ E] (k : ℕ) (D : E →L[ℝ] E)
    (hD : IsNilpotent D.toLinearMap) :
    (jetSlotSum (F := F) k D) ^ (k * Module.finrank ℝ E + 1) = 0 := by
  apply jetSlotSum_pow_eq_zero
  simpa only [hD.charpoly_eq_X_pow_finrank, map_pow, Polynomial.aeval_X] using
    D.toLinearMap.aeval_self_charpoly

/-- At a zero of a smooth vector field, only the field's derivative acts on
the first potentially nonzero derivative of a smooth function. -/
private theorem iteratedFDeriv_vectorField_of_eq_zero_global {f : E → F} {V : E → E}
    (hf : ContDiff ℝ ∞ f) (hV : ContDiff ℝ ∞ V) {x : E} (hVx : V x = 0)
    (k : ℕ) (hvanish : ∀ j < k, iteratedFDeriv ℝ j f x = 0) :
    iteratedFDeriv ℝ k (fun y => fderiv ℝ f y (V y)) x =
      jetSlotSum k (fderiv ℝ V x) (iteratedFDeriv ℝ k f x) := by
  ext1 v
  let H (p : ℝ × E) := p.2 + p.1 • V p.2
  let G := f ∘ H
  have hH : ContDiff ℝ ∞ H :=
    contDiff_snd.add (contDiff_fst.smul (hV.comp contDiff_snd))
  have hG : ContDiff ℝ ∞ G := hf.comp hH
  have hdG (y : E) : fderiv ℝ G (0, y) (1, 0) = fderiv ℝ f y (V y) := by
    have hc : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 y)
    have hd₁ := (hG.differentiable (by simp) (0, y)).hasFDerivAt.comp_hasDerivAt 0 hc
    have hd₂ : HasDerivAt (fun t : ℝ => y + t • V y) (V y) 0 := by
      simpa only [id_eq, one_smul] using
        (((hasDerivAt_id (0 : ℝ)).smul_const (V y)).const_add y)
    have hd₃ := (hf.differentiable (by simp) y).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd₂
      (by simp : y = y + (0 : ℝ) • V y)
    exact hd₁.unique hd₃
  have hd := hasDerivAt_iteratedFDeriv_slice hG k 0 x v
  simp_rw [hdG] at hd
  have heq (t : ℝ) : iteratedFDeriv ℝ k (fun y => G (t, y)) x v =
      iteratedFDeriv ℝ k f x (fun j => v j + t • fderiv ℝ V x (v j)) := by
    let S : E → E := fun y => y + t • V y
    have hS : ContDiff ℝ ∞ S := contDiff_id.add (contDiff_const.smul hV)
    have hSx : S x = x := by simp [S, hVx]
    have hDS : fderiv ℝ S x = ContinuousLinearMap.id ℝ E + t • fderiv ℝ V x :=
      ((hasFDerivAt_id x).add ((hV.differentiable (by simp) x).hasFDerivAt.const_smul t)).fderiv
    change iteratedFDeriv ℝ k (f ∘ S) x v = _
    rw [iteratedFDeriv_comp_of_lower_eq_zero hf.contDiffAt hS.contDiffAt k
      (fun j hj => by rw [hSx]; exact hvanish j hj) v, hSx, hDS]
    rfl
  have hc : HasDerivAt (fun t : ℝ => fun j => v j + t • fderiv ℝ V x (v j))
      (fun j => fderiv ℝ V x (v j)) 0 := by
    apply hasDerivAt_pi.mpr
    intro j
    simpa only [id_eq, one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const (fderiv ℝ V x (v j))).const_add (v j))
  have hc₀ : v = (fun j => v j + (0 : ℝ) • fderiv ℝ V x (v j)) := by simp
  let A := iteratedFDeriv ℝ k f x
  have hA := (A.hasFDerivAt v).comp_hasDerivAt_of_eq 0 hc hc₀
  have h := (hd.congr_of_eventuallyEq (Eventually.of_forall fun t => (heq t).symm)).unique hA
  simpa only [A, ContinuousMultilinearMap.linearDeriv_apply, jetSlotSum_apply] using h

private theorem exists_contDiff_eventuallyEq [FiniteDimensional ℝ E]
    {s : Set E} (hs : IsOpen s) {V : E → F} (hV : ContDiffOn ℝ ∞ V s) {x : E} (hx : x ∈ s) :
    ∃ W : E → F, ContDiff ℝ ∞ W ∧ W =ᶠ[𝓝 x] V := by
  obtain ⟨δ, hδ, hδs⟩ := Euclidean.nhds_basis_closedBall.mem_iff.1 (hs.mem_nhds hx)
  let b : ContDiffBump (toEuclidean x) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  let c : E → ℝ := b ∘ toEuclidean
  have hc : ContDiff ℝ ∞ c := b.contDiff.comp (ContinuousLinearEquiv.contDiff _)
  have hcs : tsupport c ⊆ s := by
    refine (tsupport_comp_subset_preimage b (ContinuousLinearEquiv.continuous _)).trans ?_
    rw [b.tsupport_eq]
    exact hδs
  refine ⟨fun y => c y • V y, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ s
    · exact hc.contDiffAt.smul (hV.contDiffAt (hs.mem_nhds hy))
    · have hys : y ∈ (tsupport c)ᶜ := fun h => hy (hcs h)
      refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport c).isOpen_compl.mem_nhds hys] with z hz
      rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]
  · have h := b.eventuallyEq_one.comp_tendsto (toEuclidean (E := E)).continuous.continuousAt
    filter_upwards [h] with y hy
    rw [show c y = 1 from hy, one_smul]

theorem iteratedFDeriv_vectorField_of_eq_zero [FiniteDimensional ℝ E]
    {s : Set E} (hs : IsOpen s) {f : E → F} {V : E → E}
    (hf : ContDiff ℝ ∞ f) (hV : ContDiffOn ℝ ∞ V s) {x : E} (hx : x ∈ s) (hVx : V x = 0)
    (k : ℕ) (hvanish : ∀ j < k, iteratedFDeriv ℝ j f x = 0) :
    iteratedFDeriv ℝ k (fun y => fderiv ℝ f y (V y)) x =
      jetSlotSum k (fderiv ℝ V x) (iteratedFDeriv ℝ k f x) := by
  obtain ⟨W, hW, he⟩ := exists_contDiff_eventuallyEq hs hV hx
  have hWe : (fun y => fderiv ℝ f y (W y)) =ᶠ[𝓝 x] fun y => fderiv ℝ f y (V y) :=
    he.mono fun y hy => congrArg (fderiv ℝ f y) hy
  rw [← (hWe.iteratedFDeriv ℝ k).eq_of_nhds, ← he.fderiv_eq]
  exact iteratedFDeriv_vectorField_of_eq_zero_global hf hW (he.eq_of_nhds.trans hVx) k hvanish

/-- A multiplier vanishing at the base point contributes zero to the leading jet. -/
theorem iteratedFDeriv_mul_eq_zero_of_lower_eq_zero [FiniteDimensional ℝ E]
    {s : Set E} (hs : IsOpen s) {f b : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hb : ContDiffOn ℝ ∞ b s) {x : E} (hx : x ∈ s) (hbx : b x = 0)
    (k : ℕ) (hflat : ∀ j < k, iteratedFDeriv ℝ j f x = 0) :
    iteratedFDeriv ℝ k (fun y => f y * b y) x = 0 := by
  obtain ⟨c, hc, he⟩ := exists_contDiff_eventuallyEq hs hb hx
  have he' : (fun y => f y * c y) =ᶠ[𝓝 x] fun y => f y * b y :=
    he.mono fun y hy => congrArg (f y * ·) hy
  rw [← (he'.iteratedFDeriv ℝ k).eq_of_nhds]
  have h := norm_iteratedFDeriv_mul_le hf hc x (n := k) (by simp)
  have hz : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) c x‖) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    rcases hik.lt_or_eq with hil | rfl
    · rw [hflat i hil, norm_zero, mul_zero, zero_mul]
    · rw [Nat.sub_self, norm_iteratedFDeriv_zero, he.eq_of_nhds.trans hbx, norm_zero, mul_zero]
  simpa only [hz, norm_le_zero_iff] using h

universe u v

/-- The leading jet of a derivative along a vanishing vector field is the
sum of its linearized actions on the slots, with a uniform nilpotence
exponent when the linearization is nilpotent. -/
def VectorFieldLeadingJetStatement : Prop :=
  ∀ (E : Type u) (F : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (s : Set E), IsOpen s →
    ∀ (f : E → F) (V : E → E), ContDiff ℝ ∞ f → ContDiffOn ℝ ∞ V s →
    ∀ x ∈ s, V x = 0 → ∀ k : ℕ, (∀ j < k, iteratedFDeriv ℝ j f x = 0) →
      iteratedFDeriv ℝ k (fun y => fderiv ℝ f y (V y)) x =
        jetSlotSum k (fderiv ℝ V x) (iteratedFDeriv ℝ k f x) ∧
      (IsNilpotent (fderiv ℝ V x).toLinearMap →
        (jetSlotSum (F := F) k (fderiv ℝ V x)) ^ (k * Module.finrank ℝ E + 1) = 0)

theorem vectorFieldLeadingJet : VectorFieldLeadingJetStatement.{u, v} := by
  intro E F _ _ _ _ _ s hs f V hf hV x hx hVx k hflat
  exact ⟨iteratedFDeriv_vectorField_of_eq_zero hs hf hV hx hVx k hflat,
    jetSlotSum_finrank_pow_eq_zero k (fderiv ℝ V x)⟩

end Langlands.HarmonicAnalysis
