import Langlands.HarmonicAnalysis.Distribution.FlatProductJets
import Langlands.HarmonicAnalysis.Distribution.ProductTestJets
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Transformation of a transverse derivative when the lower jets vanish -/

noncomputable section

open Function Set TopologicalSpace
open scoped ContDiff Distributions

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

private theorem orderedFinpartition_eq_atomic_of_length {n : ℕ}
    (c : OrderedFinpartition n) (h : c.length = n) :
    c = OrderedFinpartition.atomic n := by
  rcases c with ⟨length, size, size_pos, emb, emb_mono, parts_mono, parts_disj, parts_cover⟩
  change length = n at h
  subst length
  let c : OrderedFinpartition n :=
    ⟨n, size, size_pos, emb, emb_mono, parts_mono, parts_disj, parts_cover⟩
  have hlast (i : Fin n) : emb i ⟨size i - 1, Nat.sub_one_lt_of_lt (size_pos i)⟩ = i :=
    parts_mono.apply_eq
  have hemb (i : Fin n) (j : Fin (size i)) : emb i j = i := by
    let k := emb i j
    have hinj := c.emb_injective
      (a₁ := ⟨i, j⟩) (a₂ := ⟨k, ⟨size k - 1, Nat.sub_one_lt_of_lt (size_pos k)⟩⟩)
    have heq := hinj (hlast k).symm
    exact (congrArg Sigma.fst heq).symm
  have hsize : size = fun _ => 1 := by
    funext i
    refine c.partSize_eq_one_of_range_emb_eq_singleton (i := i) (j := i) ?_
    change range (emb i) = {i}
    ext k
    simp only [mem_range, mem_singleton_iff, hemb]
    exact ⟨fun ⟨_, hki⟩ => hki.symm, fun hki => ⟨⟨0, size_pos i⟩, hki.symm⟩⟩
  subst size
  have hemb' : emb = fun i _ => i := funext fun i => funext (hemb i)
  subst emb
  rfl

section ChainRule

variable {X Y F : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- When the outer function's lower derivatives vanish at the image point, the
order-`i` composition rule uses only the inner function's first derivative. -/
theorem iteratedFDeriv_comp_of_lower_eq_zero {f : X → Y} {g : Y → F} {x : X}
    (hg : ContDiffAt ℝ ∞ g (f x)) (hf : ContDiffAt ℝ ∞ f x)
    (i : ℕ) (hzero : ∀ k < i, iteratedFDeriv ℝ k g (f x) = 0) (v : Fin i → X) :
    iteratedFDeriv ℝ i (g ∘ f) x v =
      iteratedFDeriv ℝ i g (f x) (fun k => fderiv ℝ f x (v k)) := by
  rw [iteratedFDeriv_comp hg hf (by simp)]
  simp only [FormalMultilinearSeries.taylorComp, sum_apply]
  rw [Finset.sum_eq_single_of_mem (OrderedFinpartition.atomic i) (Finset.mem_univ _)]
  · simp [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ftaylorSeries,
      OrderedFinpartition.applyOrderedFinpartition_apply, OrderedFinpartition.atomic,
      iteratedFDeriv_one_apply]
  · intro c _ hc
    have hlt : c.length < i := c.length_le.lt_of_ne fun h =>
      hc (orderedFinpartition_eq_atomic_of_length c h)
    rw [FormalMultilinearSeries.compAlongOrderedFinpartition_apply]
    change iteratedFDeriv ℝ c.length g (f x) _ = 0
    rw [hzero _ hlt]
    rfl

end ChainRule

section NormalProjection

variable {E W F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem iteratedFDeriv_succ_apply_eq_normal {f : E × W → F} (hf : ContDiff ℝ ∞ f)
    (j : ℕ) (hzero : ∀ x : E, iteratedFDeriv ℝ j f (x, 0) = 0)
    (x : E) (v : Fin (j + 1) → E × W) :
    iteratedFDeriv ℝ (j + 1) f (x, 0) v =
      iteratedFDeriv ℝ (j + 1) f (x, 0) (fun k => (0, (v k).2)) := by
  let D := iteratedFDeriv ℝ j f
  let L := ContinuousLinearMap.inl ℝ E W
  have hD : D ∘ L = 0 := funext hzero
  have hd : Differentiable ℝ D :=
    hf.differentiable_iteratedFDeriv (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
  have hderiv := ((hd (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
  rw [hD, fderiv_zero] at hderiv
  let M := iteratedFDeriv ℝ (j + 1) f (x, 0)
  have hfirst (u : Fin (j + 1) → E × W) (hu : (u 0).2 = 0) : M u = 0 := by
    have hu' : L (u 0).1 = u 0 := Prod.ext rfl hu.symm
    have hz := congrArg (fun A : E →L[ℝ] (E × W) [×j]→L[ℝ] F => A (u 0).1) hderiv.symm
    change fderiv ℝ D (x, 0) (L (u 0).1) = 0 at hz
    change iteratedFDeriv ℝ (j + 1) f (x, 0) u = 0
    rw [iteratedFDeriv_succ_apply_left, ← hu', hz, zero_apply]
  have hslot (u : Fin (j + 1) → E × W) (k : Fin (j + 1)) (hu : (u k).2 = 0) :
      M u = 0 := by
    have hperm := Langlands.Analysis.iteratedFDeriv_comp_perm_of_contDiffAt
      (hf.contDiffAt (x := (x, 0))) (by simp) u (Equiv.swap 0 k)
    change M (u ∘ Equiv.swap 0 k) = M u at hperm
    rw [← hperm]
    exact hfirst _ (by simpa using hu)
  let vT : Fin (j + 1) → E × W := fun k => ((v k).1, 0)
  let vN : Fin (j + 1) → E × W := fun k => (0, (v k).2)
  have hv : v = vT + vN := funext fun k => Prod.ext (by simp [vT, vN]) (by simp [vT, vN])
  change M v = M vN
  conv_lhs => rw [hv]
  change M.toMultilinearMap (vT + vN) = M vN
  rw [M.toMultilinearMap.map_add_univ, Finset.sum_eq_single_of_mem ∅ (Finset.mem_univ _)]
  · rw [Finset.piecewise_empty]
    rfl
  · intro s _ hs
    obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    exact hslot (s.piecewise vT vN) k (by simp [Finset.piecewise, hk, vT])

end NormalProjection

variable {E W E' W' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup W'] [NormedSpace ℝ W']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U' : Opens E'} {V' : Opens W'}

/-- The derivative in the transverse input directions, projected to the
transverse output directions. -/
def productNormalDerivative (H : E × W → E' × W') (x : E) : W →L[ℝ] W' :=
  (ContinuousLinearMap.snd ℝ E' W').comp
    ((fderiv ℝ H (x, 0)).comp (ContinuousLinearMap.inr ℝ E W))

@[simp]
theorem productNormalDerivative_apply (H : E × W → E' × W') (x : E) (v : W) :
    productNormalDerivative H x v = (fderiv ℝ H (x, 0) (0, v)).2 := rfl

/-- The first potentially nonzero transverse derivative of a pullback is obtained
by applying the normal component of the derivative of the change of coordinates. -/
theorem transverseProductJet_comp_of_lower_eq_zero
    (f : 𝓓(productTestDomain U' V', F)) {H : E × W → E' × W'} {x : E} {x' : E'}
    (hH : ContDiffAt ℝ ∞ H (x, 0)) (hH0 : H (x, 0) = (x', 0))
    (i : ℕ) (hzero : ∀ k < i, transverseProductJetCLM k f = 0) (v : Fin i → W) :
    iteratedFDeriv ℝ i (f ∘ H) (x, 0) (fun k => (0, v k)) =
      transverseProductJetCLM i f x' (fun k => productNormalDerivative H x (v k)) := by
  have hflat (k : ℕ) (hk : k < i) (y : E') : iteratedFDeriv ℝ k f (y, 0) = 0 := by
    refine iteratedFDeriv_eq_zero_of_transverseJets f.contDiff k ?_ k le_rfl y
    intro z l hl u
    rw [← transverseProductJetCLM_apply, hzero l (hl.trans_lt hk)]
    rfl
  have hHflat (k : ℕ) (hk : k < i) : iteratedFDeriv ℝ k f (H (x, 0)) = 0 :=
    hH0 ▸ hflat k hk x'
  rw [iteratedFDeriv_comp_of_lower_eq_zero f.contDiff.contDiffAt hH i hHflat,
    hH0, transverseProductJetCLM_apply]
  simp only [productNormalDerivative_apply]
  cases i with
  | zero => simp
  | succ j =>
    exact iteratedFDeriv_succ_apply_eq_normal f.contDiff j (hflat j (Nat.lt_succ_self _)) x' _

end Langlands.HarmonicAnalysis
