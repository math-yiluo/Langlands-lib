import Langlands.Theta.Real.Metaplectic.BigCell
import Langlands.Analysis.FDerivOfCurves

/-!
# The metaplectic group is a covering group of `Sp_{2l}(ℝ)`

* `hasFDerivAt_bigCellSection` (internal): `g ↦ bigCellSection g f ∈ L²` is Fréchet differentiable at
  `g = 1`, with derivative `X ↦ bigCellSectionDeriv X f` (from the derivatives along curves).
* `RealMetaplecticGroup.eventually_weilSchwartz_eq_bigCellSection`: near `1`, the Schwartz operator
  of `g` is the explicit operator `bigCellSection (proj g)` (the other element over `proj g` has the
  opposite operator, which is far from the identity).
* `T2Space`: the topology separates points.
* `RealMetaplecticGroup.isCoveringMap_proj`: `proj` is a covering map. It is a quotient map with
  discrete kernel `{1, negOne}`: a local section over the identity is
  `s ↦ (s, bigCellSection s)`, continuous by the derivative estimate.
-/

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix Filter Topology FourierTransform
open scoped Real ContDiff RealInnerProductSpace

namespace Langlands.Theta

open Langlands.Theta.Real.Internal

variable {l : Type} [Fintype l] [DecidableEq l]

namespace Real

namespace Internal

omit [DecidableEq l] in
theorem quadMul_add (S T : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) (g : RealSchwartz l) : quadMul (S + T) g = quadMul S g + quadMul T g := by
  ext x
  simp only [quadMul_apply, _root_.add_apply, _root_.add_apply, inner_add_right]
  push_cast
  ring

omit [DecidableEq l] in
theorem quadMul_smul (c : ℝ) (S : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) (g : RealSchwartz l) : quadMul (c • S) g = c • quadMul S g := by
  ext x
  simp only [quadMul_apply, _root_.smul_apply, _root_.smul_apply, inner_smul_right, Complex.real_smul]
  push_cast
  ring

omit [DecidableEq l] in
theorem vectorFieldDeriv_add (H K : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) (g : RealSchwartz l) : vectorFieldDeriv (H + K) g = vectorFieldDeriv H g + vectorFieldDeriv K g := by
  ext x
  simp only [vectorFieldDeriv_apply, _root_.add_apply, _root_.add_apply, map_add]

omit [DecidableEq l] in
theorem vectorFieldDeriv_smul (c : ℝ) (H : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) (g : RealSchwartz l) : vectorFieldDeriv (c • H) g = c • vectorFieldDeriv H g := by
  ext x
  simp only [vectorFieldDeriv_apply, _root_.smul_apply, _root_.smul_apply, map_smul]

def qdLin (f : RealSchwartz l) : Matrix (l ⊕ l) (l ⊕ l) ℝ →ₗ[ℝ] RealSchwartz l where
  toFun X := bigCellSectionDeriv X f
  map_add' X Y := by
    have ht : (X + Y).toBlocks₁₁ = X.toBlocks₁₁ + Y.toBlocks₁₁ := Matrix.ext fun _ _ => rfl
    simp only [bigCellSectionDeriv, map_add, neg_add, quadMul_add, vectorFieldDeriv_add, ht, trace_add, add_div, ofReal_add, add_smul]
    abel
  map_smul' c X := by
    have ht : (c • X).toBlocks₁₁ = c • X.toBlocks₁₁ := Matrix.ext fun _ _ => rfl
    have hc : ((c • X.toBlocks₁₁.trace / 2 : ℝ) : ℂ) • f = c • (((X.toBlocks₁₁.trace / 2 : ℝ) : ℂ) • f) := by
      rw [smul_eq_mul, mul_div_assoc, ofReal_mul, mul_smul, Complex.coe_smul]
    have hn : ∀ S : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l, -(c • S) = c • -S := fun S => (smul_neg c S).symm
    simp only [bigCellSectionDeriv, map_smul, hn, quadMul_smul, vectorFieldDeriv_smul, ht, trace_smul, RingHom.id_apply]
    rw [hc, (fourierCLM ℂ (RealSchwartz l)).map_smul_of_tower, smul_sub, smul_add, smul_add]

theorem qd_sum (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (f : RealSchwartz l) : ∑ a, ∑ b, X a b • bigCellSectionDeriv (Matrix.single a b 1) f = bigCellSectionDeriv X f := by
  show _ = qdLin f X
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [show Matrix.single a b (X a b) = X a b • Matrix.single a b (1 : ℝ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul]
  rfl

theorem hasDerivAt_det_one {M : ℝ → l → l → ℝ} {X : l → l → ℝ} (h : HasDerivAt M X 0) (h0 : Matrix.of (M 0) = 1) :
    HasDerivAt (fun t => (Matrix.of (M t)).det) (Matrix.of X).trace 0 := by
  have hd : DifferentiableAt ℝ (fun N : l → l → ℝ => (Matrix.of N).det) (M 0) := by
    simp only [Matrix.det_apply', Matrix.of_apply]
    exact DifferentiableAt.fun_sum fun σ _ => (((contDiff_prod (n := 1) (f := fun i (N : l → l → ℝ) => N (σ i) i)
      fun i _ => contDiff_apply_apply ℝ (E := ℝ) (σ i) i).differentiable one_ne_zero) _).const_mul _
  have h1 := hd.hasFDerivAt.comp_hasDerivAt 0 h
  have h2 : HasDerivAt (fun t : ℝ => M 0 + t • X) X 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (M 0)
  have h3 := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 h2 (by simp)
  let p := (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • (Matrix.of X).map Polynomial.C)).divX.divX
  have h4 : HasDerivAt (fun t : ℝ => 1 + (Matrix.of X).trace * t + p.eval t * t ^ 2) (Matrix.of X).trace 0 :=
    ((((hasDerivAt_id (0 : ℝ)).const_mul _).const_add 1).fun_add
      ((p.hasDerivAt 0).fun_mul (hasDerivAt_pow 2 0))).congr_deriv (by simp)
  have h5 := h3.unique (h4.congr_of_eventuallyEq (.of_forall fun t => by
    refine Eq.trans ?_ (Matrix.det_one_add_smul t (Matrix.of X))
    rw [← h0]
    rfl))
  exact h5 ▸ h1

theorem curve {g : ℝ → (l ⊕ l) → (l ⊕ l) → ℝ} {X : (l ⊕ l) → (l ⊕ l) → ℝ} (g0 : Matrix.of (g 0) = 1)
    (hg : HasDerivAt g X 0) (f : RealSchwartz l) :
    HasDerivAt (fun t => schwartzToL2 l (bigCellSection (Matrix.of (g t)) f)) (schwartzToL2 l (bigCellSectionDeriv (Matrix.of X) f)) 0 := by
  have hd : ∀ i j : l → l ⊕ l, HasDerivAt (fun t => blockCLM i j (Matrix.of (g t))) (blockCLM i j (Matrix.of X)) 0 := fun i j =>
    (LinearMap.toContinuousLinearMap
      ((blockCLM i j).comp (Matrix.ofLinearEquiv ℝ).toLinearMap)).hasFDerivAt.comp_hasDerivAt 0 hg
  let A : ℝ → EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l := fun t => blockCLM Sum.inl Sum.inl (Matrix.of (g t))
  let c : ℝ → ℝ := fun t => (√|(Matrix.of (g t)).toBlocks₁₁.det|)⁻¹
  have eA : ∀ t, (A t).det = (Matrix.of (g t)).toBlocks₁₁.det := fun t => det_blockCLM _ _ _
  have A0 : A 0 = 1 := by simp only [A, g0, block_inl_inl_one]
  have h0 : IsUnit (A 0) := A0 ▸ isUnit_one
  have hopen : ∀ᶠ u in 𝓝 0, IsUnit (A u) := (hd _ _).continuousAt.eventually (Units.isOpen.mem_nhds h0)
  have hdet : ∀ t, IsUnit (A t) → (Ring.inverse (A t)).det * (A t).det = 1 := fun t ht => by
    have := congrArg ContinuousLinearMap.det (Ring.inverse_mul_cancel _ ht)
    simpa [ContinuousLinearMap.det] using this
  have hc : ∀ t, IsUnit (A t) → c t ^ 2 = |(Ring.inverse (A t)).det| := fun t ht => by
    rw [eq_inv_of_mul_eq_one_left (hdet t ht), abs_inv, inv_pow, Real.sq_sqrt (abs_nonneg _), eA]
  have d0 : (Matrix.of (g 0)).toBlocks₁₁.det = 1 := by
    rw [← eA, A0]
    simp [ContinuousLinearMap.det]
  have c0 : c 0 = 1 := by simp only [c, d0]; simp
  have hD : HasDerivAt (fun t => (Matrix.of (g t)).toBlocks₁₁.det) (Matrix.of X).toBlocks₁₁.trace 0 :=
    hasDerivAt_det_one (M := fun t a b => g t (.inl a) (.inl b)) (X := fun a b => X (.inl a) (.inl b))
      (hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => hasDerivAt_pi.1 (hasDerivAt_pi.1 hg _) _)
      (by
        ext a b
        have := congrFun (congrFun g0 (.inl a)) (.inl b)
        simpa [Matrix.one_apply] using this)
  have hcd : HasDerivAt c (-((Matrix.of X).toBlocks₁₁.trace / 2)) 0 := by
    have hp : 0 < (Matrix.of (g 0)).toBlocks₁₁.det := by rw [d0]; exact one_pos
    have h1 := (hD.sqrt hp.ne').inv (Real.sqrt_pos.2 hp).ne'
    refine (h1.congr_of_eventuallyEq ?_).congr_deriv (by simp only [d0]; simp)
    filter_upwards [hD.continuousAt.eventually (lt_mem_nhds hp)] with t ht
    simp only [c, abs_of_pos ht]
    rfl
  have h1 : HasDerivAt (fun t => Ring.inverse (A t)) (-blockCLM Sum.inl Sum.inl (Matrix.of X)) 0 := by
    have h2 := (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l)ˣ)).comp_hasDerivAt_of_eq 0
      (hd Sum.inl Sum.inl) A0.symm
    exact h2.congr_deriv (by
      simp only [_root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply, inv_one, Units.val_one,
        one_mul, mul_one])
  obtain ⟨Q, hQ, hQ'⟩ := hasL2DerivAt_bigCellOp h1 (hd Sum.inl Sum.inr) (hd Sum.inr Sum.inl) hcd
    (hopen.mono fun u hu => ⟨hu.ringInverse, hc u hu⟩)
  have h3 := hQ' (by rw [A0, Ring.inverse_one]) (by rw [g0, block_inl_inr_one]) (by rw [g0, block_inr_inl_one]) c0 f
  refine (hQ f).congr_deriv (congrArg _ ?_)
  rw [h3, bigCellSectionDeriv, ofReal_neg, neg_smul, sub_eq_add_neg]

/-- The derivative of `bigCellSection` along a differentiable family of matrices through `1`. -/
theorem hasFDerivAt_bigCellSection (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : E → Matrix (l ⊕ l) (l ⊕ l) ℝ) (m' : l ⊕ l → l ⊕ l → E →L[ℝ] ℝ) (x₀ : E) (h0 : m x₀ = 1)
    (hm : ∀ a b, HasFDerivAt (fun x => m x a b) (m' a b) x₀) (f : RealSchwartz l) :
    HasFDerivAt (fun x => schwartzToL2 l (bigCellSection (m x) f))
      (∑ a, ∑ b, (m' a b).smulRight (schwartzToL2 l (bigCellSectionDeriv (Matrix.single a b 1) f)))
      x₀ := by
  let L : ((l ⊕ l) → (l ⊕ l) → ℝ) →L[ℝ] RealL2 l := LinearMap.toContinuousLinearMap
    ((((schwartzToL2 l).restrictScalars ℝ).toLinearMap.comp (qdLin f)).comp (Matrix.ofLinearEquiv ℝ).toLinearMap)
  have hL : ∀ X, L X = schwartzToL2 l (bigCellSectionDeriv (Matrix.of X) f) := fun X => rfl
  have h1 : HasFDerivAt (fun g : (l ⊕ l) → (l ⊕ l) → ℝ => schwartzToL2 l (bigCellSection (Matrix.of g) f)) L (fun a b => m x₀ a b) :=
    Langlands.hasFDerivAt_of_curves fun c v c0 hc => curve (by rw [c0, h0]; rfl) hc f
  have h2 : HasFDerivAt (fun x => fun a b => m x a b)
      (ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b => m' a b) x₀ :=
    hasFDerivAt_pi.2 fun a => hasFDerivAt_pi.2 fun b => hm a b
  refine (h1.comp x₀ h2).congr_fderiv ?_
  ext1 v
  rw [ContinuousLinearMap.comp_apply, hL, ← qd_sum]
  simp only [map_sum, _root_.sum_apply, ContinuousLinearMap.smulRight_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  exact ((schwartzToL2 l).restrictScalars ℝ).map_smul _ _

omit [Fintype l] in
theorem toBlocks₁₁_one' : (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ).toBlocks₁₁ = 1 := by
  ext a b
  simp [Matrix.toBlocks₁₁, Matrix.one_apply]

theorem sec_one : bigCellSection (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 := by
  rw [bigCellSection, block_inl_inl_one, block_inl_inr_one, block_inr_inl_one, toBlocks₁₁_one', Matrix.det_one, abs_one, Real.sqrt_one, inv_one,
    Ring.inverse_one, bigCellOp_one]

theorem eventually_det_pos : ∀ᶠ s in 𝓝 (1 : Matrix.symplecticGroup l ℝ), 0 < s.1.toBlocks₁₁.det := by
  have hc : Continuous fun s : Matrix.symplecticGroup l ℝ => s.1.toBlocks₁₁.det :=
    Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j =>
      continuous_subtype_val.matrix_elem (Sum.inl i) (Sum.inl j))
  have h1 : (1 : Matrix.symplecticGroup l ℝ).1.toBlocks₁₁.det = 1 := by
    rw [show (1 : Matrix.symplecticGroup l ℝ).1 = 1 from rfl, toBlocks₁₁_one', Matrix.det_one]
  have h2 : ∀ᶠ y in 𝓝 ((1 : Matrix.symplecticGroup l ℝ).1.toBlocks₁₁.det), (0 : ℝ) < y := lt_mem_nhds (by rw [h1]; exact one_pos)
  exact (hc.tendsto 1).eventually h2

theorem eventually_det_pos_G : ∀ᶠ g in 𝓝 (1 : RealMetaplecticGroup l), 0 < (RealMetaplecticGroup.proj g).1.toBlocks₁₁.det := by
  have h := RealMetaplecticGroup.continuous_proj.tendsto (1 : RealMetaplecticGroup l)
  rw [map_one] at h
  exact h.eventually eventually_det_pos

theorem tendsto_sec (f : RealSchwartz l) :
    Tendsto (fun s : Matrix.symplecticGroup l ℝ => schwartzToL2 l (bigCellSection s.1 f)) (𝓝 1) (𝓝 (schwartzToL2 l f)) := by
  let m' : (l ⊕ l) → (l ⊕ l) → (((l ⊕ l) → (l ⊕ l) → ℝ) →L[ℝ] ℝ) := fun a b =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : l ⊕ l => ℝ) b).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : l ⊕ l => (l ⊕ l) → ℝ) a)
  have h := hasFDerivAt_bigCellSection ((l ⊕ l) → (l ⊕ l) → ℝ) (fun x => Matrix.of x) m' (fun a b => (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b) rfl
    (fun a b => (m' a b).hasFDerivAt.congr_of_eventuallyEq (Eventually.of_forall fun x => rfl)) f
  have h2 : schwartzToL2 l (bigCellSection (Matrix.of fun a b => (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b) f) = schwartzToL2 l f := by
    rw [show (Matrix.of fun a b => (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b) = 1 from rfl, sec_one, one_apply_eq_self]
  have h3 : Tendsto (fun x : (l ⊕ l) → (l ⊕ l) → ℝ => schwartzToL2 l (bigCellSection (Matrix.of x) f))
      (𝓝 (fun a b => (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b)) (𝓝 (schwartzToL2 l f)) := by
    convert h.continuousAt.tendsto using 2
    exact h2.symm
  have hc : Continuous fun s : Matrix.symplecticGroup l ℝ => (fun a b => (s.1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b : (l ⊕ l) → (l ⊕ l) → ℝ) :=
    continuous_pi fun a => continuous_pi fun b => continuous_subtype_val.matrix_elem a b
  have h4 : Tendsto (fun s : Matrix.symplecticGroup l ℝ => (fun a b => (s.1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b : (l ⊕ l) → (l ⊕ l) → ℝ)) (𝓝 1)
      (𝓝 (fun a b => (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b)) := hc.tendsto 1
  exact h3.comp h4

omit [DecidableEq l] in
theorem exists_sch_ne : ∃ f : RealSchwartz l, schwartzToL2 l f ≠ 0 := by
  obtain ⟨φ, hφ⟩ := exists_ne_zero (l := l) 0
  refine ⟨φ, fun h => hφ ?_⟩
  have : φ = 0 := injective_toLp 2 volume
    (show φ.toLp 2 volume = (0 : RealSchwartz l).toLp 2 volume by
      rw [← SchwartzMap.toLpCLM_apply (𝕜 := ℂ), ← SchwartzMap.toLpCLM_apply (𝕜 := ℂ), h, map_zero])
  simp [this]

end Internal

/-- Near the identity the Schwartz operator is the explicit big-cell operator. -/
theorem _root_.Langlands.Theta.RealMetaplecticGroup.eventually_weilSchwartz_eq_bigCellSection :
    ∀ᶠ g in 𝓝 (1 : RealMetaplecticGroup l),
      RealMetaplecticGroup.weilSchwartz g = bigCellSection (RealMetaplecticGroup.proj g).1 := by
  obtain ⟨ε, -, hker, hεom⟩ : ∃ ε : RealMetaplecticGroup l, ε ≠ 1 ∧ (∀ g, RealMetaplecticGroup.proj g = 1 ↔ g = 1 ∨ g = ε) ∧
      ∀ f, RealMetaplecticGroup.weil ε f = -f :=
    ⟨RealMetaplecticGroup.negOne, RealMetaplecticGroup.negOne_ne_one, fun _ => RealMetaplecticGroup.proj_eq_one_iff,
      RealMetaplecticGroup.weil_negOne⟩
  obtain ⟨f, hf⟩ := exists_sch_ne (l := l)
  have hv : 0 < ‖schwartzToL2 l f‖ := norm_pos_iff.2 hf
  have hom : ∀ᶠ g in 𝓝 (1 : RealMetaplecticGroup l), ‖RealMetaplecticGroup.weil g (schwartzToL2 l f) - schwartzToL2 l f‖ < ‖schwartzToL2 l f‖ := by
    have h := (RealMetaplecticGroup.continuous_weil (schwartzToL2 l f)).tendsto (1 : RealMetaplecticGroup l)
    rw [map_one] at h
    exact (tendsto_iff_norm_sub_tendsto_zero.1 h).eventually (gt_mem_nhds hv)
  have hsec : ∀ᶠ g in 𝓝 (1 : RealMetaplecticGroup l), ‖schwartzToL2 l (bigCellSection (RealMetaplecticGroup.proj g).1 f) - schwartzToL2 l f‖ < ‖schwartzToL2 l f‖ := by
    have h := RealMetaplecticGroup.continuous_proj.tendsto (1 : RealMetaplecticGroup l)
    rw [map_one] at h
    exact (tendsto_iff_norm_sub_tendsto_zero.1 ((tendsto_sec f).comp h)).eventually (gt_mem_nhds hv)
  filter_upwards [eventually_det_pos_G, hom, hsec] with g h1 h2 h3
  obtain ⟨g', c, hg', hU, hc⟩ := RealMetaplecticGroup.exists_weilSchwartz_eq_smul_bigCellSection (RealMetaplecticGroup.proj g) h1.ne'
  rw [hc h1, one_smul] at hU
  have hk : RealMetaplecticGroup.proj (g * g'⁻¹) = 1 := by rw [map_mul, map_inv, hg', mul_inv_cancel]
  rcases (hker _).1 hk with h | h
  · rw [mul_inv_eq_one.1 h, hU, hg']
  · exfalso
    have hg : g = ε * g' := mul_inv_eq_iff_eq_mul.1 h
    have e1 : RealMetaplecticGroup.weil g = RealMetaplecticGroup.weil ε * RealMetaplecticGroup.weil g' := by rw [hg, map_mul]
    have e : RealMetaplecticGroup.weil g (schwartzToL2 l f) = -schwartzToL2 l (bigCellSection (RealMetaplecticGroup.proj g).1 f) := by
      rw [e1]
      show RealMetaplecticGroup.weil ε (RealMetaplecticGroup.weil g' (schwartzToL2 l f)) = _
      rw [hεom, RealMetaplecticGroup.Internal.weil_toLp_aux, hU]
    rw [e] at h2
    have h4 : ‖schwartzToL2 l f + schwartzToL2 l f‖ ≤
        ‖schwartzToL2 l (bigCellSection (RealMetaplecticGroup.proj g).1 f) - schwartzToL2 l f‖ + ‖-schwartzToL2 l (bigCellSection (RealMetaplecticGroup.proj g).1 f) - schwartzToL2 l f‖ := by
      have := norm_add_le (schwartzToL2 l (bigCellSection (RealMetaplecticGroup.proj g).1 f) - schwartzToL2 l f) (-schwartzToL2 l (bigCellSection (RealMetaplecticGroup.proj g).1 f) - schwartzToL2 l f)
      have e2 : schwartzToL2 l (bigCellSection (RealMetaplecticGroup.proj g).1 f) - schwartzToL2 l f + (-schwartzToL2 l (bigCellSection (RealMetaplecticGroup.proj g).1 f) - schwartzToL2 l f) =
          -(schwartzToL2 l f + schwartzToL2 l f) := by abel
      rwa [e2, norm_neg] at this
    have h5 : ‖schwartzToL2 l f + schwartzToL2 l f‖ = 2 * ‖schwartzToL2 l f‖ := by
      rw [← two_smul ℂ (schwartzToL2 l f), norm_smul]
      norm_num
    linarith

namespace Internal

theorem isInducing_F :
    IsInducing (fun g : RealMetaplecticGroup l => ((RealMetaplecticGroup.proj g, fun f => RealMetaplecticGroup.weil g f) : Matrix.symplecticGroup l ℝ × (RealL2 l → RealL2 l))) := ⟨rfl⟩

end Internal

/-- The metaplectic group is Hausdorff. -/
instance _root_.Langlands.Theta.RealMetaplecticGroup.instT2Space : T2Space (RealMetaplecticGroup l) := by
  refine T2Space.of_injective_continuous (f := fun g : RealMetaplecticGroup l => ((RealMetaplecticGroup.proj g, fun f => RealMetaplecticGroup.weil g f) : Matrix.symplecticGroup l ℝ × (RealL2 l → RealL2 l)))
    ?_ isInducing_F.continuous
  intro g h hgh
  simp only [Prod.mk.injEq] at hgh
  obtain ⟨h1, h2⟩ := hgh
  have hu : RealMetaplecticGroup.weil g = RealMetaplecticGroup.weil h := LinearIsometryEquiv.ext fun f => congrFun h2 f
  have hU : RealMetaplecticGroup.weilSchwartz g = RealMetaplecticGroup.weilSchwartz h := ContinuousLinearMap.ext fun f => by
    apply injective_toLp 2 volume
    show schwartzToL2 l (RealMetaplecticGroup.weilSchwartz g f) = schwartzToL2 l (RealMetaplecticGroup.weilSchwartz h f)
    rw [← RealMetaplecticGroup.Internal.weil_toLp_aux, ← RealMetaplecticGroup.Internal.weil_toLp_aux, hu]
  exact Subtype.ext (p := (· ∈ RealMetaplecticGroup.subgroup l)) (Prod.ext h1 (Prod.ext hu (Units.ext hU)))

/-- The projection to `Sp_{2l}(ℝ)` is a covering map. -/
theorem _root_.Langlands.Theta.RealMetaplecticGroup.isCoveringMap_proj :
    IsCoveringMap (RealMetaplecticGroup.proj : RealMetaplecticGroup l → Matrix.symplecticGroup l ℝ) := by
  obtain ⟨ε, -, hker, -⟩ : ∃ ε : RealMetaplecticGroup l, ε ≠ 1 ∧ (∀ g, RealMetaplecticGroup.proj g = 1 ↔ g = 1 ∨ g = ε) ∧
      ∀ f, RealMetaplecticGroup.weil ε f = -f :=
    ⟨RealMetaplecticGroup.negOne, RealMetaplecticGroup.negOne_ne_one, fun _ => RealMetaplecticGroup.proj_eq_one_iff,
      RealMetaplecticGroup.weil_negOne⟩
  have hσ : ∀ s : Matrix.symplecticGroup l ℝ, ∃ g : RealMetaplecticGroup l, 0 < s.1.toBlocks₁₁.det → RealMetaplecticGroup.proj g = s ∧ RealMetaplecticGroup.weilSchwartz g = bigCellSection s.1 := fun s => by
    by_cases h : 0 < s.1.toBlocks₁₁.det
    · obtain ⟨g, c, h1, h2, h3⟩ := RealMetaplecticGroup.exists_weilSchwartz_eq_smul_bigCellSection s h.ne'
      exact ⟨g, fun _ => ⟨h1, by rw [h2, h3 h, one_smul]⟩⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose σ hσ using hσ
  have hd : DenseRange (schwartzToL2 l) := by
    have h := SchwartzMap.denseRange_toLpCLM (E := EuclideanSpace ℝ l) (F := ℂ)
      (μ := (volume : Measure (EuclideanSpace ℝ l))) (p := 2) ENNReal.ofNat_ne_top
    convert h using 1
    funext g
    rfl
  have hv : ∀ v : RealL2 l, Tendsto (fun s => RealMetaplecticGroup.weil (σ s) v) (𝓝 1) (𝓝 v) := fun v => by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    obtain ⟨φ, hφ⟩ := hd.exists_dist_lt v (show 0 < δ / 3 by positivity)
    have h1 := (Metric.tendsto_nhds.1 (tendsto_sec φ)) (δ / 3) (by positivity)
    filter_upwards [h1, eventually_det_pos] with s hs1 hs2
    have e : RealMetaplecticGroup.weil (σ s) (schwartzToL2 l φ) = schwartzToL2 l (bigCellSection s.1 φ) := by rw [RealMetaplecticGroup.Internal.weil_toLp_aux, (hσ s hs2).2]
    calc dist (RealMetaplecticGroup.weil (σ s) v) v ≤ dist (RealMetaplecticGroup.weil (σ s) v) (RealMetaplecticGroup.weil (σ s) (schwartzToL2 l φ)) +
          dist (RealMetaplecticGroup.weil (σ s) (schwartzToL2 l φ)) (schwartzToL2 l φ) + dist (schwartzToL2 l φ) v := dist_triangle4 _ _ _ _
      _ < δ := by
        rw [(RealMetaplecticGroup.weil (σ s)).isometry.dist_eq, e, dist_comm (schwartzToL2 l φ) v]
        linarith
  have key : Tendsto σ (𝓝 1) (𝓝 1) := by
    have hpr : Tendsto (fun s => RealMetaplecticGroup.proj (σ s)) (𝓝 (1 : Matrix.symplecticGroup l ℝ)) (𝓝 1) :=
      tendsto_id.congr' (eventually_det_pos.mono fun s hs => (hσ s hs).1.symm)
    have h2 : Tendsto (fun s => ((RealMetaplecticGroup.proj (σ s), fun f => RealMetaplecticGroup.weil (σ s) f) : Matrix.symplecticGroup l ℝ × (RealL2 l → RealL2 l))) (𝓝 1)
        (𝓝 ((RealMetaplecticGroup.proj (1 : RealMetaplecticGroup l), fun f => RealMetaplecticGroup.weil (1 : RealMetaplecticGroup l) f))) := by
      rw [map_one, map_one]
      refine hpr.prodMk_nhds (tendsto_pi_nhds.2 fun v => ?_)
      simpa using hv v
    exact isInducing_F.tendsto_nhds_iff.2 h2
  have hopen : IsOpenMap (RealMetaplecticGroup.proj : RealMetaplecticGroup l → Matrix.symplecticGroup l ℝ) := by
    intro U hU
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨g, hg, rfl⟩
    have hc : Tendsto (fun t : Matrix.symplecticGroup l ℝ => (RealMetaplecticGroup.proj g)⁻¹ * t) (𝓝 (RealMetaplecticGroup.proj g)) (𝓝 1) := by
      have : Continuous fun t : Matrix.symplecticGroup l ℝ => (RealMetaplecticGroup.proj g)⁻¹ * t :=
        Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) fun t => ((RealMetaplecticGroup.proj g)⁻¹ * t).2
      simpa using this.tendsto (RealMetaplecticGroup.proj g)
    have h1 : Tendsto (fun t => g * σ ((RealMetaplecticGroup.proj g)⁻¹ * t)) (𝓝 (RealMetaplecticGroup.proj g)) (𝓝 g) := by
      have := ((continuous_const_mul g).tendsto 1).comp (key.comp hc)
      rwa [mul_one] at this
    filter_upwards [h1 (hU.mem_nhds hg), hc.eventually eventually_det_pos] with t ht ht'
    exact ⟨_, ht, by rw [map_mul, (hσ _ ht').1, mul_inv_cancel_left]⟩
  have hker' : ((RealMetaplecticGroup.proj : RealMetaplecticGroup l →* Matrix.symplecticGroup l ℝ).ker : Set (RealMetaplecticGroup l)) = {1, ε} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hker g
  have hdisc : IsDiscrete ((RealMetaplecticGroup.proj : RealMetaplecticGroup l →* Matrix.symplecticGroup l ℝ).ker : Set (RealMetaplecticGroup l)) := by
    rw [hker']
    exact ((Set.finite_singleton ε).insert 1).isDiscrete
  have hq : IsQuotientMap (RealMetaplecticGroup.proj : RealMetaplecticGroup l → Matrix.symplecticGroup l ℝ) := hopen.isQuotientMap RealMetaplecticGroup.continuous_proj RealMetaplecticGroup.proj_surjective
  exact (hq.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom hdisc).isCoveringMap

end Real

end Langlands.Theta
