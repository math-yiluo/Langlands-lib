import Langlands.Theta.Real.WeylAlgebra
import Langlands.Analysis.OneParameterSubgroup

/-!
# Intertwiners of the real Schrödinger representation

`Intertwines s S`: the operator `S` of Schwartz space preserves `L²` norms and carries the
Schrödinger operator of `w` to that of `s w`. For such `S`, surjective:

* `Intertwines.comm_schrodingerDeriv`: for linear `s`, `S` also intertwines the derived operators,
  `S (schrodingerDeriv w f) = schrodingerDeriv (s w) (S f)` (differentiate the matrix
  coefficients `⟪φ, S(t w) f⟫` at `t = 0`);
* `Intertwines.continuous`: for invertible linear `s`, `S` is continuous for the Schwartz topology
  (every seminorm is controlled by `L²` norms of images under the Weyl algebra, which `S` permutes);
* `Intertwines.exists_eq_smul`: for `s = id`, `S` is a scalar (a Schur lemma: `S` preserves the
  matrix coefficients `⟪φ, ρ(0, q) f⟫ = 𝓕(φ̄ f)(-q)`, hence `S φ̄ · S f = φ̄ f` pointwise, so `S` is
  multiplication by a function, which commutes with translations only if it is constant).

`oscillatorDeriv_mem_weylAlgebra`: the infinitesimal oscillator operators lie in the Weyl algebra.
-/

noncomputable section

open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff FourierTransform

namespace Langlands.Theta

open Langlands.Theta.Real.Internal

variable {l : Type} [Fintype l]

namespace Real

namespace Internal

theorem hasDerivAt_rhoFun_at (w : l ⊕ l → ℝ) (f : RealSchwartz l) (x : EuclideanSpace ℝ l) (t : ℝ) :
    HasDerivAt (fun t : ℝ => rhoFun (t • w) f x) (rhoFun (t • w) (schrodingerDeriv w f) x) t := by
  have h1 := ((hasDerivAt_rhoFun w f (x + translationPart (t • w))).const_mul (schrodingerPhase (t • w) x))
  have h2 : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  have h3 := HasDerivAt.scomp_of_eq (𝕜 := ℝ) (𝕜' := ℝ) t h1 h2 (by simp)
  rw [one_smul] at h3
  refine h3.congr_of_eventuallyEq (.of_forall fun s => ?_)
  have h4 := congrFun (rhoFun_rhoFun (t • w) ((s - t) • w) f) x
  have h5 : sympl (t • w) ((s - t) • w) = 0 := by
    simp only [sympl, translationPart_smul, modulationPart_smul, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm (translationPart w) (modulationPart w)]
    ring
  rw [h5, ← add_smul, add_sub_cancel] at h4
  simpa [rhoFun] using h4.symm

theorem inner_toLp_schrodingerL2 (w : l ⊕ l → ℝ) (φ f : RealSchwartz l) :
    inner ℂ (φ.toLp 2 volume) (schrodingerL2 w (f.toLp 2 volume)) = ∫ x, inner ℂ (φ x) (rhoFun w f x) := by
  apply integral_congr_ae
  filter_upwards [φ.coeFn_toLp 2 volume, (coeFn_schrodingerL2_eq_rhoFun w (f.toLp 2 volume)).trans (rhoFun_congr w (f.coeFn_toLp 2 volume))]
    with x h1 h2
  rw [h1, h2]

theorem hasDerivAt_inner_schrodingerL2 (w : l ⊕ l → ℝ) (φ f : RealSchwartz l) :
    HasDerivAt (fun t : ℝ => inner ℂ (φ.toLp 2 volume) (schrodingerL2 (t • w) (f.toLp 2 volume)))
      (inner ℂ (φ.toLp 2 volume) ((schrodingerDeriv w f).toLp 2 volume)) 0 := by
  have hc : ∀ (u : l ⊕ l → ℝ) (g : RealSchwartz l), Continuous fun x => inner ℂ (φ x) (rhoFun u g x) := fun u g =>
    φ.continuous.inner ((continuous_schrodingerPhase u).mul (g.continuous.comp (continuous_add_const _)))
  have hb : ∀ (u : l ⊕ l → ℝ) (g : RealSchwartz l) (x), ‖inner ℂ (φ x) (rhoFun u g x)‖ ≤
      ‖φ x‖ * SchwartzMap.seminorm ℝ 0 0 g := fun u g x => by
    refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [rhoFun, norm_mul, norm_schrodingerPhase, one_mul]
    exact norm_le_seminorm ℝ g _
  have := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (s := Set.univ) (x₀ := (0 : ℝ))
    (F := fun t x => inner ℂ (φ x) (rhoFun (t • w) f x))
    (F' := fun t x => inner ℂ (φ x) (rhoFun (t • w) (schrodingerDeriv w f) x))
    (bound := fun x => ‖φ x‖ * SchwartzMap.seminorm ℝ 0 0 (schrodingerDeriv w f)) Filter.univ_mem
    (.of_forall fun t => (hc _ _).aestronglyMeasurable)
    ((φ.integrable.norm.mul_const _).mono' (hc _ _).aestronglyMeasurable (.of_forall (hb _ f)))
    (hc _ _).aestronglyMeasurable (.of_forall fun x t _ => hb _ _ x) (φ.integrable.norm.mul_const _)
    (.of_forall fun x t _ => ((innerSL ℂ (φ x)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_rhoFun_at w f x t))).2
  simp only [inner_toLp_schrodingerL2, inner_toL2_toL2_eq]
  simpa only [zero_smul, rhoFun_zero] using this

end Internal

/-- `S` preserves the `L²` norm of Schwartz functions and carries the Schrödinger operator of `w`
to that of `s w`: `S ∘ schrodingerSchwartz w = schrodingerSchwartz (s w) ∘ S`. -/
structure Intertwines (s : (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (S : RealSchwartz l →ₗ[ℂ] RealSchwartz l) :
    Prop where
  norm_toLp : ∀ f, ‖(S f).toLp 2 volume‖ = ‖f.toLp 2 volume‖
  comm : ∀ w f, S (schrodingerSchwartz w f) = schrodingerSchwartz (s w) (S f)

namespace Internal

theorem schwartz_eq_schrodingerSchwartz {w : l ⊕ l → ℝ} {f g : RealSchwartz l}
    (hg : ⇑g = rhoFun w f) : g = schrodingerSchwartz w f :=
  SchwartzMap.ext fun x => by rw [hg, coe_schrodingerSchwartz_eq_rhoFun]

end Internal

/-- The intertwining relation in the form of the proofs. -/
theorem Intertwines.comm_rhoFun {s} {S : RealSchwartz l →ₗ[ℂ] RealSchwartz l} (h : Intertwines s S)
    (w : l ⊕ l → ℝ) (f g : RealSchwartz l) (hg : ⇑g = rhoFun w f) : ⇑(S g) = rhoFun (s w) (S f) := by
  rw [schwartz_eq_schrodingerSchwartz hg, h.comm, coe_schrodingerSchwartz_eq_rhoFun]

/-- An `L²`-isometric operator intertwining the operators `rhoFun` intertwines. -/
theorem Intertwines.of_rhoFun {s} {S : RealSchwartz l →ₗ[ℂ] RealSchwartz l}
    (hn : ∀ f, ‖(S f).toLp 2 volume‖ = ‖f.toLp 2 volume‖)
    (hi : ∀ w (f g : RealSchwartz l), ⇑g = rhoFun w f → ⇑(S g) = rhoFun (s w) (S f)) :
    Intertwines s S :=
  ⟨hn, fun w f => SchwartzMap.ext fun x => by
    rw [hi w f _ (coe_schrodingerSchwartz_eq_rhoFun w f), coe_schrodingerSchwartz_eq_rhoFun]⟩

/-- An intertwiner preserves the `L²` inner products of Schwartz functions. -/
theorem Intertwines.inner {s} {S : RealSchwartz l →ₗ[ℂ] RealSchwartz l} (h : Intertwines s S) (f g : RealSchwartz l) :
    inner ℂ ((S f).toLp 2 volume) ((S g).toLp 2 volume) = inner ℂ (f.toLp 2 volume) (g.toLp 2 volume) := by
  have e : ∀ (u v : RealSchwartz l) (c : ℂ), u.toLp 2 volume + c • v.toLp 2 volume = (u + c • v).toLp 2 volume := fun u v c => by
    simp only [← SchwartzMap.toLpCLM_apply (𝕜 := ℂ), map_add, map_smul]
  have e' : ∀ (u v : RealSchwartz l) (c : ℂ), u.toLp 2 volume - c • v.toLp 2 volume = (u - c • v).toLp 2 volume := fun u v c => by
    simp only [← SchwartzMap.toLpCLM_apply (𝕜 := ℂ), map_sub, map_smul]
  have e1 := e (S f) (S g) 1
  have e2 := e' (S f) (S g) 1
  have e3 := e f g 1
  have e4 := e' f g 1
  simp only [one_smul] at e1 e2 e3 e4
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, e1, e2, e3, e4, e, e, e', e', ← map_add, ← map_sub,
    ← map_smul, ← map_add, ← map_sub, h.norm_toLp, h.norm_toLp, h.norm_toLp, h.norm_toLp]

namespace Internal

theorem exists_schwartz_eq_rhoFun (w : l ⊕ l → ℝ) (f : RealSchwartz l) : ∃ g : RealSchwartz l, ⇑g = rhoFun w f := by
  have ht : Function.HasTemperateGrowth (schrodingerPhase w) := by
    have h2 : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => ⟪modulationPart w, x⟫ + ⟪translationPart w, modulationPart w⟫ / 2 :=
      (innerSL ℝ (modulationPart w)).hasTemperateGrowth.add (Function.HasTemperateGrowth.const _)
    have h3 := hasTemperateGrowth_fourierCharℂ.comp h2
    convert h3 using 1
    funext x
    simp only [schrodingerPhase, Function.comp, fourierCharℂ_apply]
    congr 1
    push_cast
    ring
  refine ⟨smulLeftCLM ℂ (schrodingerPhase w) (compSubConstCLM ℂ (-translationPart w) f), ?_⟩
  funext x
  rw [smulLeftCLM_apply_apply ht]
  simp [rhoFun]

theorem toLp_eq_schrodingerL2 {w : l ⊕ l → ℝ} {f g : RealSchwartz l} (h : ⇑g = rhoFun w f) : g.toLp 2 volume = schrodingerL2 w (f.toLp 2 volume) := by
  refine Lp.ext ((g.coeFn_toLp 2 volume).trans ?_)
  rw [h]
  exact ((coeFn_schrodingerL2_eq_rhoFun w _).trans (rhoFun_congr w (f.coeFn_toLp 2 volume))).symm

theorem eq_of_inner {u v : RealSchwartz l} (h : ∀ φ : RealSchwartz l, inner ℂ (φ.toLp 2 volume) (u.toLp 2 volume) =
    inner ℂ (φ.toLp 2 volume) (v.toLp 2 volume)) : u = v := by
  apply injective_toLp 2 volume
  have := h (u - v)
  rw [← sub_eq_zero, ← inner_sub_right, ← toLpCLM_apply (𝕜 := ℂ), map_sub] at this
  exact sub_eq_zero.1 (inner_self_eq_zero.1 this)

end Internal

/-- A surjective intertwiner along a linear `s` also intertwines the derived Schrödinger operators. -/
theorem Intertwines.comm_schrodingerDeriv {s : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)} {S : RealSchwartz l →ₗ[ℂ] RealSchwartz l} (h : Intertwines s S)
    (hs : Function.Surjective S) (w : l ⊕ l → ℝ) (f : RealSchwartz l) : S (schrodingerDeriv w f) = schrodingerDeriv (s w) (S f) := by
  refine eq_of_inner fun φ => ?_
  obtain ⟨φ', rfl⟩ := hs φ
  have d1 := hasDerivAt_inner_schrodingerL2 w φ' f
  have d2 := hasDerivAt_inner_schrodingerL2 (s w) (S φ') (S f)
  rw [h.inner]
  refine d1.unique (d2.congr_of_eventuallyEq (.of_forall fun t => ?_))
  obtain ⟨g, hg⟩ := exists_schwartz_eq_rhoFun (t • w) f
  simp only
  rw [← toLp_eq_schrodingerL2 hg, ← map_smul, ← toLp_eq_schrodingerL2 (h.comm_rhoFun _ _ _ hg), h.inner]

variable [DecidableEq l] in
/-- A surjective intertwiner along an invertible linear `s` is continuous for the Schwartz topology. -/
theorem Intertwines.continuous {s : (l ⊕ l → ℝ) ≃ₗ[ℝ] (l ⊕ l → ℝ)} {S : RealSchwartz l →ₗ[ℂ] RealSchwartz l} (h : Intertwines s S)
    (hs : Function.Surjective S) : Continuous S := by
  have hA : ∀ A ∈ weylAlgebra l, ∃ A' : RealSchwartz l →L[ℂ] RealSchwartz l, ∀ f, A (S f) = S (A' f) := fun A hA => by
    refine weylAlgebra_induction (P := fun A => ∃ A' : RealSchwartz l →L[ℂ] RealSchwartz l, ∀ f, A (S f) = S (A' f)) ⟨1, fun _ => rfl⟩ ?_
      ⟨0, fun f => by simp⟩ ?_ ?_ hA
    · rintro A w ⟨A', h'⟩
      refine ⟨A' * schrodingerDeriv (s.symm w), fun f => ?_⟩
      have := Intertwines.comm_schrodingerDeriv (s := s.toLinearMap) h hs (s.symm w) f
      simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
      rw [mul_apply_eq_comp, mul_apply_eq_comp, ← this, h']
    · rintro A B ⟨A', h1⟩ ⟨B', h2⟩
      exact ⟨A' + B', fun f => by simp [h1, h2]⟩
    · rintro c A ⟨A', h1⟩
      exact ⟨c • A', fun f => by simp [h1]⟩
  refine (schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).continuous_of_continuous_comp S fun kn => ?_
  obtain ⟨A, hAm, hb⟩ := exists_seminorm_le_sum_norm_toLp (l := l) kn.1 kn.2
  choose A' hA' using fun r => hA _ (hAm r)
  refine Seminorm.continuous_of_continuousAt_zero (𝕝 := ℂ) ?_
  have hc : Continuous fun f : RealSchwartz l => ∑ r, ‖schwartzToL2 l (A' r f)‖ := by fun_prop
  have h0 := hc.tendsto 0
  simp only [map_zero, norm_zero, Finset.sum_const_zero] at h0
  rw [ContinuousAt, map_zero]
  refine squeeze_zero (fun f => apply_nonneg _ _) (fun f => ?_) h0
  have := hb (S f)
  simp only [hA', h.norm_toLp] at this
  exact this

namespace Internal

theorem exists_ne_zero (x : EuclideanSpace ℝ l) : ∃ φ : RealSchwartz l, φ x ≠ 0 := by
  obtain ⟨f, h1, h2, h3, -, h4⟩ := exists_contDiff_tsupport_subset (n := ⊤) (s := Set.univ) (x := x) Filter.univ_mem
  refine ⟨(h2.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)).toSchwartzMap (ofRealCLM.contDiff.comp h3), ?_⟩
  show ((f x : ℝ) : ℂ) ≠ 0
  simp [h4]

end Internal

/-- Schur's lemma for the Schrödinger representation on Schwartz space: a surjective intertwiner
along the identity is a scalar. -/
theorem Intertwines.exists_eq_smul {S : RealSchwartz l →ₗ[ℂ] RealSchwartz l} (h : Intertwines id S) (hs : Function.Surjective S) : ∃ c : ℂ, ∀ f, S f = c • f := by
  have h1 : ∀ (φ f : RealSchwartz l) x, (starRingEnd ℂ) (S φ x) * S f x = (starRingEnd ℂ) (φ x) * f x := fun φ f x => by
    have key : ∀ (a b : RealSchwartz l) (q : EuclideanSpace ℝ l) (g : RealSchwartz l), ⇑g = rhoFun (Sum.elim 0 fun i => -q i) b →
        Inner.inner ℂ (a.toLp 2 volume) (g.toLp 2 volume) = 𝓕 (fun x => (starRingEnd ℂ) (a x) * b x) q := fun a b q g hg => by
      rw [toLp_eq_schrodingerL2 hg, inner_toLp_schrodingerL2, Real.fourier_eq']
      refine integral_congr_ae (.of_forall fun y => ?_)
      have e1 : translationPart (l := l) (Sum.elim 0 fun i => -q i) = 0 := rfl
      have e2 : modulationPart (l := l) (Sum.elim 0 fun i => -q i) = -q := rfl
      simp only [rhoFun, schrodingerPhase, e1, e2, inner_zero_left, mul_zero, add_zero, inner_neg_left, smul_eq_mul, RCLike.inner_apply,
        real_inner_comm y q]
      push_cast
      ring_nf
    have hi : ∀ a b : RealSchwartz l, Integrable (fun x => (starRingEnd ℂ) (a x) * b x) ∧
        Continuous (fun x => (starRingEnd ℂ) (a x) * b x) := fun a b =>
      ⟨b.integrable.bdd_mul (c := SchwartzMap.seminorm ℂ 0 0 a) (continuous_conj.comp a.continuous).aestronglyMeasurable
        (.of_forall fun x => by simpa using a.norm_le_seminorm ℂ x), (continuous_conj.comp a.continuous).mul b.continuous⟩
    set u := fun x => (starRingEnd ℂ) (S φ x) * S f x - (starRingEnd ℂ) (φ x) * f x with hu
    have hz : 𝓕 u = 0 := by
      funext q
      obtain ⟨g, hg⟩ := exists_schwartz_eq_rhoFun (Sum.elim 0 fun i => -q i) f
      have := h.inner φ g
      rw [key _ _ q _ (h.comm_rhoFun _ _ _ hg), key _ _ q _ hg, Real.fourier_eq', Real.fourier_eq'] at this
      rw [Real.fourier_eq', hu]
      simp only [smul_sub]
      have hb : ∀ a b : RealSchwartz l, Integrable fun v => cexp (((-2 * π * ⟪v, q⟫ : ℝ) : ℂ) * I) • ((starRingEnd ℂ) (a v) * b v) :=
        fun a b => (hi a b).1.bdd_mul (c := 1) (by fun_prop) (.of_forall fun v => (norm_exp_ofReal_mul_I _).le)
      rw [integral_sub (hb _ _) (hb _ _), this, sub_self]
      rfl
    have := Continuous.fourierInv_fourier_eq (f := u) ((hi _ _).2.sub (hi _ _).2) ((hi _ _).1.sub (hi _ _).1)
      (by rw [hz]; exact integrable_zero _ _ _)
    rw [hz] at this
    have h3 := congrFun this x
    rw [Real.fourierInv_eq] at h3
    simp only [Pi.zero_apply, smul_zero, integral_zero] at h3
    exact sub_eq_zero.1 h3.symm
  have h2 : ∀ x, ∃ m : ℂ, ∀ f : RealSchwartz l, S f x = m * f x := fun x => by
    obtain ⟨φ, hφ⟩ := exists_ne_zero x
    obtain ⟨φ', rfl⟩ := hs φ
    have hn : (starRingEnd ℂ) (S φ' x) ≠ 0 := by simpa using hφ
    refine ⟨(starRingEnd ℂ) (φ' x) / (starRingEnd ℂ) (S φ' x), fun f => ?_⟩
    rw [div_mul_eq_mul_div, eq_div_iff hn, mul_comm, h1]
  obtain ⟨m, hm⟩ := h2 0
  refine ⟨m, fun f => SchwartzMap.ext fun x => ?_⟩
  obtain ⟨g, hg⟩ := exists_schwartz_eq_rhoFun (Sum.elim (fun i => x i) 0) f
  have e1 : translationPart (l := l) (Sum.elim (fun i => x i) 0) = x := rfl
  have e2 : modulationPart (l := l) (Sum.elim (fun i => x i) 0) = 0 := rfl
  have := hm g
  rw [h.comm_rhoFun _ _ _ hg, hg] at this
  simpa [rhoFun, schrodingerPhase, e1, e2] using this

variable [DecidableEq l] in
/-- The infinitesimal oscillator operators lie in the Weyl algebra. -/
theorem oscillatorDeriv_mem_weylAlgebra (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) : oscillatorDeriv X ∈ weylAlgebra l :=
  Subalgebra.smul_mem _ (sum_mem fun _ _ => sum_mem fun _ _ => Subalgebra.smul_mem _
    (add_mem (mul_mem (schrodingerDeriv_mem_weylAlgebra _) (schrodingerDeriv_mem_weylAlgebra _)) (mul_mem (schrodingerDeriv_mem_weylAlgebra _) (schrodingerDeriv_mem_weylAlgebra _))) _) _

end Real

end Langlands.Theta
