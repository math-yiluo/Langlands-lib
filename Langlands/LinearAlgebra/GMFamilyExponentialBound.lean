import Langlands.LinearAlgebra.GMFamilySmoothExtension
import Langlands.LinearAlgebra.GMFamilyGramVolume
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.ReImTopology

/-! # A uniform bound for `c_M` of an exponential family near the imaginary axis

For points `y_P` with the family property, the function `c_M` of the `(G, M)`-family
`e^{λ(y_P)}` is evaluated at the spectral parameters `λ = i(Λ + sμ)`, `s ∈ ℂ`, where `Λ` and `μ`
are real functionals on `a` and `μ` does not vanish on any simple root. The raw sum
`expShift R a y Λ μ s = ∑_S e^{i(Λ + sμ)(y_S)} θ_S(Λ + sμ)⁻¹` is meaningful where all linear
factors `Λ(v) + sμ(v)` are nonzero; as a function of `s` it agrees there with an entire function
(removable singularities at the finitely many real points `−Λ(v)/μ(v)`). The main result
`norm_expShift_le` bounds the raw sum on the strip part `Re s = 0`, `|Im s| ≤ 1`, at the points
where all linear factors are nonzero, by an explicit constant independent of `Λ`; the proof
applies the maximum modulus principle to the entire extension. -/

noncomputable section

open scoped RealInnerProductSpace Topology ContDiff
open Filter Finset Classical Complex

namespace Langlands.GMFamily

section Removable

/-- **Removable singularities on the real line.** A function that is holomorphic off finitely
many real points, meromorphic at them, and agrees off them on the real line with a continuous
function, coincides off these points with an entire function. -/
theorem exists_entire_of_real_poles {g : ℂ → ℂ} {P : Finset ℝ}
    (hg : ∀ s : ℂ, (∀ p ∈ P, s ≠ (p : ℂ)) → DifferentiableAt ℂ g s)
    (hmero : ∀ p ∈ P, MeromorphicAt g (p : ℂ))
    {f : ℝ → ℂ} (hf : Continuous f) (hgf : ∀ σ : ℝ, σ ∉ P → g σ = f σ) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ s : ℂ, (∀ p ∈ P, s ≠ (p : ℂ)) → G s = g s := by
  -- the real points near a pole other than the pole avoid all poles
  have hnear (p : ℝ) : ∀ᶠ σ in 𝓝[≠] p, σ ∉ P := by
    have hclosed : IsClosed ((P.erase p : Set ℝ)) := (P.erase p).finite_toSet.isClosed
    have hopen : (↑(P.erase p) : Set ℝ)ᶜ ∈ 𝓝 p :=
      hclosed.isOpen_compl.mem_nhds (by simp)
    filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with σ h1 h2
    intro hσ
    exact h1 (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨h2, hσ⟩))
  have hext : ∀ p ∈ P, ∃ h : ℂ → ℂ, AnalyticAt ℂ h (p : ℂ) ∧ g =ᶠ[𝓝[≠] (p : ℂ)] h := by
    intro p hp
    refine (hmero p hp).meromorphicOrderAt_nonneg_iff.mp ?_
    by_contra hneg
    have h1 := tendsto_cobounded_of_meromorphicOrderAt_neg (lt_of_not_ge hneg)
    have hreal : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[≠] p) (𝓝[≠] (p : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      simpa using hσ
    have h2 : Tendsto (fun σ : ℝ => g σ) (𝓝[≠] p) (Bornology.cobounded ℂ) := h1.comp hreal
    have h3 : Tendsto (fun σ : ℝ => g σ) (𝓝[≠] p) (𝓝 (f p)) := by
      refine (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [hnear p] with σ hσ
      exact (hgf σ hσ).symm
    exact h3.not_tendsto (Metric.disjoint_nhds_cobounded _) h2
  choose! h hh hgh using hext
  let Pc : Set ℂ := (fun p : ℝ => (p : ℂ)) '' (P : Set ℝ)
  have hPc : IsClosed Pc := ((P : Set ℝ).toFinite.image _).isClosed
  have hmemPc (s : ℂ) : s ∈ Pc ↔ s.im = 0 ∧ s.re ∈ P := by
    constructor
    · rintro ⟨p, hp, rfl⟩
      simpa using hp
    · rintro ⟨him, hre⟩
      exact ⟨s.re, hre, Complex.ext (by simp) (by simp [him])⟩
  have hnotPc (s : ℂ) : s ∉ Pc ↔ ∀ p ∈ P, s ≠ (p : ℂ) := by
    constructor
    · intro hs p hp he
      exact hs ⟨p, hp, he.symm⟩
    · rintro hs ⟨p, hp, rfl⟩
      exact hs p hp rfl
  let G : ℂ → ℂ := fun s => if s.im = 0 ∧ s.re ∈ P then h s.re s else g s
  refine ⟨G, fun s => ?_, fun s hs => ?_⟩
  · by_cases hs : s.im = 0 ∧ s.re ∈ P
    · -- near a pole `G` coincides with the analytic extension
      have hsp : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hs.1])
      have hA : AnalyticAt ℂ (h s.re) s := by rw [hsp]; exact hh _ hs.2
      have hev : G =ᶠ[𝓝 s] h s.re := by
        have hne : ∀ᶠ z in 𝓝[≠] s, z ∉ Pc := by
          have hclosed : IsClosed (Pc \ {s}) :=
            (((P : Set ℝ).toFinite.image _).sdiff).isClosed
          have hopen : (Pc \ {s})ᶜ ∈ 𝓝 s := hclosed.isOpen_compl.mem_nhds (by simp)
          filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with z h1 h2
          intro hz
          exact h1 ⟨hz, h2⟩
        have hgz : g =ᶠ[𝓝[≠] s] h s.re := by
          have := hgh _ hs.2
          rwa [← hsp] at this
        rw [← nhdsNE_sup_pure s, Filter.EventuallyEq, Filter.eventually_sup]
        refine ⟨?_, ?_⟩
        · filter_upwards [hne, hgz] with z hz hz'
          have : ¬ (z.im = 0 ∧ z.re ∈ P) := fun h' => hz ((hmemPc z).mpr h')
          simp only [G, this, ↓reduceIte]
          exact hz'
        · simp [G, hs]
      exact (hA.differentiableAt).congr_of_eventuallyEq hev
    · have hsPc : s ∉ Pc := fun h' => hs ((hmemPc s).mp h')
      have hev : G =ᶠ[𝓝 s] g := by
        filter_upwards [hPc.isOpen_compl.mem_nhds hsPc] with z hz
        have : ¬ (z.im = 0 ∧ z.re ∈ P) := fun h' => hz ((hmemPc z).mpr h')
        simp only [G, this, ↓reduceIte]
      exact (hg s ((hnotPc s).mp hsPc)).congr_of_eventuallyEq hev
  · have hsPc : s ∉ Pc := (hnotPc s).mpr hs
    have : ¬ (s.im = 0 ∧ s.re ∈ P) := fun h' => hsPc ((hmemPc s).mpr h')
    simp only [G, this, ↓reduceIte]

end Removable

section Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {R : Finset E} {a : Submodule ℝ E}

variable (a) in
/-- `θ_S(Λ + s μ) = gram(S)⁻¹ ∏_v i(Λ(v) + sμ(v))` at the complex parameter `s`, that is, `θ_S` at
the spectral parameter `i(Λ + sμ)`. -/
def thetaShift (S : Finset E) (Λ μ : StrongDual ℝ a) (s : ℂ) : ℂ :=
  ((gramVolume fun v : simpleRoots a S => ((v : a) : E) : ℝ) : ℂ)⁻¹ *
    ∏ v : simpleRoots a S, (I * ((Λ (v : a) : ℂ) + s * (μ (v : a) : ℂ)))

variable (R a) in
/-- The raw sum `∑_S e^{i(Λ + sμ)(y_S)} θ_S(Λ + s μ)⁻¹` for the exponential family of the points
`y`, at the complex parameter `s` (spectral parameter `i(Λ + sμ)`). Where all linear factors
`Λ(v) + sμ(v)` are nonzero it is `c_M(Λ + sμ)`; elsewhere the vanishing denominators are inverted
to `0`, so the raw sum need not agree there with the holomorphic extension of `c_M`. -/
def expShift (y : Finset E → a) (Λ μ : StrongDual ℝ a) (s : ℂ) : ℂ :=
  ∑ S ∈ parabolics R a, exp (I * ((Λ (y S) : ℂ) + s * (μ (y S) : ℂ))) * (thetaShift a S Λ μ s)⁻¹

variable (R a) in
/-- The constant `∑_S e^{|μ(y_S)|} gram(S) ∏_v |μ(v)|⁻¹` of `norm_expShift_le`. When the points
`y` give a `(G, M)`-family of exponentials and `μ(v) ≠ 0` for every simple root `v` of every
chamber, it bounds `expShift` at the points `s` with `Re s = 0`, `|Im s| ≤ 1` where all linear
factors are nonzero. Without these hypotheses it need not be a bound: the inverses `|μ(v)|⁻¹` are
`0` where `μ(v) = 0`, so a chamber having a simple root on which `μ` vanishes contributes `0` to
the sum. -/
def expShiftBound (y : Finset E → a) (μ : StrongDual ℝ a) : ℝ :=
  ∑ S ∈ parabolics R a, Real.exp |μ (y S)| *
    (gramVolume (fun v : simpleRoots a S => ((v : a) : E)) * ∏ v : simpleRoots a S, |μ (v : a)|⁻¹)

theorem thetaShift_ofReal (S : Finset E) (Λ μ : StrongDual ℝ a) (σ : ℝ) :
    thetaShift a S Λ μ σ = theta a S (Λ + σ • μ) := by
  simp [thetaShift, theta, thetaOf]

theorem expShift_ofReal (y : Finset E → a) (Λ μ : StrongDual ℝ a) (σ : ℝ) :
    expShift R a y Λ μ σ =
      cM R a (fun S Λ' => exp (I * (Λ' (y S) : ℂ))) (Λ + σ • μ) := by
  simp only [expShift, cM, thetaShift_ofReal]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp

theorem differentiable_thetaShift (S : Finset E) (Λ μ : StrongDual ℝ a) :
    Differentiable ℂ (thetaShift a S Λ μ) := by
  unfold thetaShift
  refine (differentiable_const _).mul ?_
  exact Differentiable.fun_finsetProd fun v _ =>
    (differentiable_const _).mul ((differentiable_const _).add
      (differentiable_id.mul (differentiable_const _)))

theorem thetaShift_ne_zero (hR : IsRootSet R) (ha : IsLeviSpace R a) {S : Finset E}
    (hS : S ∈ parabolics R a) {Λ μ : StrongDual ℝ a} {s : ℂ}
    (hs : ∀ v ∈ simpleRoots a S, (Λ v : ℂ) + s * (μ v : ℂ) ≠ 0) :
    thetaShift a S Λ μ s ≠ 0 := by
  have hli : LinearIndependent ℝ (fun v : simpleRoots a S => ((v : a) : E)) :=
    (linearIndependent_simpleRoots hR ha hS).map' a.subtype
      (LinearMap.ker_eq_bot.mpr a.injective_subtype)
  have hg := ((gramVolume_pos_iff _).mpr hli).ne'
  refine mul_ne_zero (inv_ne_zero (by exact_mod_cast hg))
    (Finset.prod_ne_zero_iff.mpr fun v _ => mul_ne_zero I_ne_zero (hs v v.property))

/-- On the boundary of the rectangle the linear factors stay away from zero: for `μv ≠ 0` and
`A ≥ 1 + |Λv|/|μv|`, every `z` on the boundary of `|Re z| ≤ A`, `|Im z| ≤ 1` has
`|Λv + z μv| ≥ |μv|`. -/
theorem norm_factor_ge {Λv μv A : ℝ} (hμ : μv ≠ 0) (hA : 1 + |Λv| / |μv| ≤ A) {z : ℂ}
    (hz : (|z.re| = A ∧ |z.im| ≤ 1) ∨ (|z.re| ≤ A ∧ |z.im| = 1)) :
    |μv| ≤ ‖(Λv : ℂ) + z * (μv : ℂ)‖ := by
  have hμpos : 0 < |μv| := abs_pos.mpr hμ
  rcases hz with ⟨hre, -⟩ | ⟨-, him⟩
  · have h1 : |Λv + z.re * μv| ≤ ‖(Λv : ℂ) + z * (μv : ℂ)‖ := by
      have := Complex.abs_re_le_norm ((Λv : ℂ) + z * (μv : ℂ))
      simpa using this
    have h2 : |z.re * μv| - |Λv| ≤ |Λv + z.re * μv| := by
      have := abs_sub_abs_le_abs_sub (z.re * μv) (-Λv)
      simpa [abs_neg, sub_neg_eq_add, add_comm] using this
    have h3 : |μv| + |Λv| ≤ |z.re * μv| := by
      rw [abs_mul, hre]
      have : (1 + |Λv| / |μv|) * |μv| ≤ A * |μv| := mul_le_mul_of_nonneg_right hA hμpos.le
      rw [add_mul, one_mul, div_mul_cancel₀ _ hμpos.ne'] at this
      linarith
    linarith
  · have h1 : |z.im * μv| ≤ ‖(Λv : ℂ) + z * (μv : ℂ)‖ := by
      have := Complex.abs_im_le_norm ((Λv : ℂ) + z * (μv : ℂ))
      simpa using this
    rw [abs_mul, him, one_mul] at h1
    exact h1

/-- **Uniform bound for the exponential family.** Let `y` have the family property and let `μ`
be a real functional that does not vanish on any simple root. For every `Λ` and every `s` with
`Re s = 0`, `|Im s| ≤ 1` at which all linear factors `Λ(v) + sμ(v)` are nonzero (so that the raw
sum `expShift` is `c_M(Λ + sμ)`), `‖expShift R a y Λ μ s‖ ≤ expShiftBound R a y μ`. -/
theorem norm_expShift_le (hR : IsRootSet R) (ha : IsLeviSpace R a) (y : Finset E → a)
    (hy : IsFamily R a (fun S Λ => exp (I * (Λ (y S) : ℂ)))) (μ : StrongDual ℝ a)
    (hμ : ∀ S ∈ parabolics R a, ∀ v ∈ simpleRoots a S, μ v ≠ 0) (Λ : StrongDual ℝ a)
    {s : ℂ} (hre : s.re = 0) (him : |s.im| ≤ 1)
    (hs : ∀ S ∈ parabolics R a, ∀ v ∈ simpleRoots a S, (Λ v : ℂ) + s * (μ v : ℂ) ≠ 0) :
    ‖expShift R a y Λ μ s‖ ≤ expShiftBound R a y μ := by
  let Ps := parabolics R a
  -- the real poles
  let P : Finset ℝ := Ps.biUnion fun S => (simpleRoots a S).image fun v => -(Λ v) / μ v
  have hfactor {S : Finset E} (hS : S ∈ Ps) {v : a} (hv : v ∈ simpleRoots a S) {z : ℂ}
      (hz : ∀ p ∈ P, z ≠ (p : ℂ)) : (Λ v : ℂ) + z * (μ v : ℂ) ≠ 0 := by
    intro h0
    have hμv : (μ v : ℂ) ≠ 0 := by exact_mod_cast hμ S hS v hv
    have hzv : z = ((-(Λ v) / μ v : ℝ) : ℂ) := by
      push_cast
      field_simp
      linear_combination h0
    exact hz _ (Finset.mem_biUnion.mpr ⟨S, hS, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩) hzv
  have hθ {S : Finset E} (hS : S ∈ Ps) {z : ℂ} (hz : ∀ p ∈ P, z ≠ (p : ℂ)) :
      thetaShift a S Λ μ z ≠ 0 :=
    thetaShift_ne_zero hR ha hS fun v hv => hfactor hS hv hz
  -- holomorphy off the poles
  have hdiff : ∀ z : ℂ, (∀ p ∈ P, z ≠ (p : ℂ)) → DifferentiableAt ℂ (expShift R a y Λ μ) z := by
    intro z hz
    unfold expShift
    refine DifferentiableAt.fun_sum fun S hS => ?_
    refine DifferentiableAt.mul ?_ ((differentiable_thetaShift S Λ μ z).inv (hθ hS hz))
    exact (differentiableAt_const _).mul ((differentiableAt_const _).add
      (differentiableAt_id.mul (differentiableAt_const _))) |>.cexp
  have hmero : ∀ p ∈ P, MeromorphicAt (expShift R a y Λ μ) (p : ℂ) := by
    intro p _
    unfold expShift
    refine MeromorphicAt.fun_sum fun S _ => ?_
    refine MeromorphicAt.mul ?_ ?_
    · exact (((differentiable_const _).mul ((differentiable_const _).add
        (differentiable_id.mul (differentiable_const _)))).cexp.analyticAt _).meromorphicAt
    · exact ((differentiable_thetaShift S Λ μ).analyticAt _).meromorphicAt.inv
  -- the smooth extension along the real line
  obtain ⟨F, hF, hFe⟩ := smoothExtension R a hR ha _ hy
  let f : ℝ → ℂ := fun σ => F (Λ + σ • μ)
  have hf : Continuous f := hF.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hgf : ∀ σ : ℝ, σ ∉ P → expShift R a y Λ μ σ = f σ := by
    intro σ hσ
    have hz : ∀ p ∈ P, (σ : ℂ) ≠ (p : ℂ) := fun p hp he => hσ (by
      rw [Complex.ofReal_injective he]; exact hp)
    rw [expShift_ofReal]
    refine (hFe _ fun S hS => ?_).symm
    rw [← thetaShift_ofReal]
    exact hθ hS hz
  obtain ⟨G, hG, hGg⟩ := exists_entire_of_real_poles hdiff hmero hf hgf
  -- the rectangle
  let A : ℝ := 1 + ∑ S ∈ Ps, ∑ v ∈ simpleRoots a S, |Λ v| / |μ v|
  have hA : ∀ S ∈ Ps, ∀ v ∈ simpleRoots a S, 1 + |Λ v| / |μ v| ≤ A := by
    intro S hS v hv
    have h1 : |Λ v| / |μ v| ≤ ∑ v ∈ simpleRoots a S, |Λ v| / |μ v| :=
      Finset.single_le_sum (f := fun v : a => |Λ v| / |μ v|) (fun _ _ => by positivity) hv
    have h2 : ∑ v ∈ simpleRoots a S, |Λ v| / |μ v| ≤
        ∑ S ∈ Ps, ∑ v ∈ simpleRoots a S, |Λ v| / |μ v| :=
      Finset.single_le_sum (f := fun S => ∑ v ∈ simpleRoots a S, |Λ v| / |μ v|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) hS
    simp only [A]
    linarith
  have hA1 : 1 ≤ A := by
    simp only [A]
    have := Finset.sum_nonneg (s := Ps) (f := fun S => ∑ v ∈ simpleRoots a S, |Λ v| / |μ v|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
    linarith
  let U : Set ℂ := Set.Ioo (-A) A ×ℂ Set.Ioo (-1) 1
  have hclosure : closure U = Set.Icc (-A) A ×ℂ Set.Icc (-1) 1 := by
    simp only [U, Complex.closure_reProdIm, closure_Ioo (by linarith : -A ≠ A),
      closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
  have hfront : ∀ z ∈ frontier U, (|z.re| = A ∧ |z.im| ≤ 1) ∨ (|z.re| ≤ A ∧ |z.im| = 1) := by
    intro z hz
    simp only [U, Complex.frontier_reProdIm, closure_Ioo (by linarith : -A ≠ A),
      closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1), frontier_Ioo (by linarith : -A < A),
      frontier_Ioo (by norm_num : (-1 : ℝ) < 1)] at hz
    rcases hz with hz | hz
    · obtain ⟨h1, h2⟩ := Complex.mem_reProdIm.mp hz
      right
      refine ⟨abs_le.mpr ⟨h1.1, h1.2⟩, ?_⟩
      rcases h2 with h2 | h2 <;> simp [Set.mem_singleton_iff.mp h2]
    · obtain ⟨h1, h2⟩ := Complex.mem_reProdIm.mp hz
      left
      refine ⟨?_, abs_le.mpr ⟨h2.1, h2.2⟩⟩
      rcases h1 with h1 | h1
      · rw [h1, abs_neg, abs_of_pos (by linarith)]
      · rw [Set.mem_singleton_iff.mp h1, abs_of_pos (by linarith)]
  have hbdd : Bornology.IsBounded U :=
    ((isCompact_Icc.reProdIm isCompact_Icc).isBounded).subset
      (hclosure ▸ subset_closure)
  -- the bound on the boundary
  have hbound : ∀ z ∈ frontier U, ‖G z‖ ≤ expShiftBound R a y μ := by
    intro z hz
    have hz' := hfront z hz
    have hfac : ∀ S ∈ Ps, ∀ v ∈ simpleRoots a S, |μ v| ≤ ‖(Λ v : ℂ) + z * (μ v : ℂ)‖ :=
      fun S hS v hv => norm_factor_ge (hμ S hS v hv) (hA S hS v hv) hz'
    have hnp : ∀ p ∈ P, z ≠ (p : ℂ) := by
      intro p hp hzp
      obtain ⟨S, hS, hpS⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hpS
      have h0 : (Λ v : ℂ) + z * (μ v : ℂ) = 0 := by
        rw [hzp]
        have hμv : (μ v : ℂ) ≠ 0 := by exact_mod_cast hμ S hS v hv
        push_cast
        field_simp
        ring
      have := hfac S hS v hv
      rw [h0, norm_zero] at this
      exact hμ S hS v hv (abs_nonpos_iff.mp this)
    rw [hGg z hnp]
    unfold expShift expShiftBound
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun S hS => ?_)
    rw [norm_mul]
    refine mul_le_mul ?_ ?_ (norm_nonneg _) (Real.exp_pos _).le
    · rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hre : (I * ((Λ (y S) : ℂ) + z * (μ (y S) : ℂ))).re = -(z.im * μ (y S)) := by
        simp [Complex.mul_re]
      rw [hre]
      have him1 : |z.im| ≤ 1 := by rcases hz' with ⟨-, h⟩ | ⟨-, h⟩ <;> [exact h; exact h.le]
      calc -(z.im * μ (y S)) ≤ |z.im * μ (y S)| := neg_le_abs _
        _ = |z.im| * |μ (y S)| := abs_mul _ _
        _ ≤ 1 * |μ (y S)| := mul_le_mul_of_nonneg_right him1 (abs_nonneg _)
        _ = |μ (y S)| := one_mul _
    · unfold thetaShift
      have hgv : 0 ≤ gramVolume (fun v : simpleRoots a S => ((v : a) : E)) := Real.sqrt_nonneg _
      rw [mul_inv, inv_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hgv, norm_inv, norm_prod]
      refine mul_le_mul_of_nonneg_left ?_ hgv
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_le_prod₀ (fun v _ => inv_nonneg.mpr (norm_nonneg _)) fun v _ => ?_
      rw [norm_mul, Complex.norm_I, one_mul]
      exact inv_anti₀ (abs_pos.mpr (hμ S hS v v.property)) (hfac S hS v v.property)
  have hsmem : s ∈ closure U := by
    rw [hclosure]
    refine Complex.mem_reProdIm.mpr ⟨?_, abs_le.mp him⟩
    rw [hre]
    exact ⟨by linarith, by linarith⟩
  have hsnp : ∀ p ∈ P, s ≠ (p : ℂ) := by
    intro p hp hsp
    obtain ⟨S, hS, hpS⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hpS
    apply hs S hS v hv
    rw [hsp]
    have hμv : (μ v : ℂ) ≠ 0 := by exact_mod_cast hμ S hS v hv
    push_cast
    field_simp
    ring
  rw [← hGg s hsnp]
  exact Complex.norm_le_of_forall_mem_frontier_norm_le hbdd hG.diffContOnCl hbound hsmem

end Exponential

end Langlands.GMFamily
