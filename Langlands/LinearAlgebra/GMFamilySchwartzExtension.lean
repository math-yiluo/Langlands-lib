import Langlands.LinearAlgebra.GMFamilySmoothExtension
import Langlands.LinearAlgebra.GMFamilyGramVolume
import Langlands.Analysis.SchwartzLinearDivision

/-! # `c_M` of a family of Schwartz functions (Lapid's Corollary 3)

For a `(G, M)`-family `{d_P}` of Schwartz functions on `i𝔞_M^*`, the smooth extension of
`d_M = ∑_P d_P θ_P⁻¹` is a Schwartz function. For each fixed output order `K`, its finite supremum
of Schwartz seminorms of order `K` is bounded by a constant times the sum over `P` of a finite
supremum of seminorms of order `K'` of the `d_P`, where `K'` and the constant depend on the root
set, the Levi space and `K`. -/

noncomputable section

open scoped RealInnerProductSpace SchwartzMap ContDiff NNReal
open Finset Classical

namespace Langlands.GMFamily

section SchwartzSup

variable {𝕜 : Type*} [RCLike 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

variable (𝕜) in
/-- The supremum of the Schwartz seminorms of orders `(k, n) ≤ (K, K)`. -/
def schwartzSup (K : ℕ) : Seminorm 𝕜 𝓢(X, F) :=
  (Finset.Iic (K, K)).sup (schwartzSeminormFamily 𝕜 X F)

theorem seminorm_le_schwartzSup {k n K : ℕ} (hk : k ≤ K) (hn : n ≤ K) (f : 𝓢(X, F)) :
    SchwartzMap.seminorm 𝕜 k n f ≤ schwartzSup 𝕜 K f :=
  Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily 𝕜 X F)
    (Finset.mem_Iic.mpr (Prod.mk_le_mk.mpr ⟨hk, hn⟩))

theorem schwartzSup_mono {K K' : ℕ} (h : K ≤ K') (f : 𝓢(X, F)) :
    schwartzSup 𝕜 K f ≤ schwartzSup 𝕜 K' f :=
  Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun _ hi =>
    Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily 𝕜 X F)
      (Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hi).trans (Prod.mk_le_mk.mpr ⟨h, h⟩)))

/-- The value of `schwartzSup` does not depend on the scalar field of the seminorms. -/
theorem schwartzSup_real_eq (K : ℕ) (f : 𝓢(X, F)) :
    schwartzSup ℝ K f = schwartzSup 𝕜 K f := by
  simp only [schwartzSup, Seminorm.finset_sup_apply, schwartzSeminormFamily,
    SchwartzMap.seminorm_apply]

end SchwartzSup

section ClmBound

variable {𝕜 : Type*} [RCLike 𝕜]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜 G] [SMulCommClass ℝ 𝕜 G]

/-- A continuous linear map into a Schwartz space is bounded by a finite supremum of the
seminorms that define the topology of its domain. -/
theorem exists_schwartzSup_bound {Z : Type*} [AddCommGroup Z] [Module 𝕜 Z] [TopologicalSpace Z]
    {p : SeminormFamily 𝕜 Z (ℕ × ℕ)} (hp : WithSeminorms p) (T : Z →L[𝕜] 𝓢(Y, G)) (K : ℕ) :
    ∃ K' : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z, schwartzSup 𝕜 K (T z) ≤ C * (Finset.Iic (K', K')).sup p z := by
  have h : ∀ i : ℕ × ℕ, ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ≥0, C ≠ 0 ∧
      (schwartzSeminormFamily 𝕜 Y G i).comp T.toLinearMap ≤ C • s.sup p := fun i =>
    Seminorm.bound_of_continuous hp _
      (((schwartz_withSeminorms 𝕜 Y G).continuous_seminorm i).comp T.continuous)
  choose s C _ hb using h
  let K' := ((Finset.Iic (K, K)).biUnion s).sup (fun j => max j.1 j.2)
  refine ⟨K', ∑ i ∈ Finset.Iic (K, K), (C i : ℝ), Finset.sum_nonneg fun i _ => (C i).2,
    fun z => ?_⟩
  have hsub (i : ℕ × ℕ) (hi : i ∈ Finset.Iic (K, K)) : s i ⊆ Finset.Iic (K', K') := by
    intro j hj
    have hle : max j.1 j.2 ≤ K' :=
      Finset.le_sup (f := fun j : ℕ × ℕ => max j.1 j.2) (Finset.mem_biUnion.mpr ⟨i, hi, hj⟩)
    exact Finset.mem_Iic.mpr (Prod.mk_le_mk.mpr ⟨(le_max_left _ _).trans hle,
      (le_max_right _ _).trans hle⟩)
  refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
  have h1 : schwartzSeminormFamily 𝕜 Y G i (T z) ≤ C i * (s i).sup p z :=
    le_of_le_of_eq (hb i z) (by simp [NNReal.smul_def])
  have h2 : (s i).sup p z ≤ (Finset.Iic (K', K')).sup p z :=
    Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun j hj =>
      Seminorm.le_finset_sup_apply (hsub i hi hj)
  calc schwartzSeminormFamily 𝕜 Y G i (T z) ≤ C i * (Finset.Iic (K', K')).sup p z :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (C i).2)
    _ ≤ _ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun i => (C i : ℝ)) (fun i _ => (C i).2) hi)
        (apply_nonneg _ _)

/-- Bound for a continuous linear map between Schwartz spaces. -/
theorem exists_schwartzSup_bound_schwartz {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedSpace 𝕜 H] [SMulCommClass ℝ 𝕜 H]
    (T : 𝓢(W, H) →L[𝕜] 𝓢(Y, G)) (K : ℕ) :
    ∃ K' : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ f, schwartzSup 𝕜 K (T f) ≤ C * schwartzSup 𝕜 K' f :=
  exists_schwartzSup_bound (schwartz_withSeminorms 𝕜 W H) T K

end ClmBound

section Division

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Seminorm bound for the division by a nonzero linear form `ℓ` of Schwartz functions vanishing
on `ker ℓ` (Lapid's Lemma 7). -/
theorem exists_division_bound (ℓ : X →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (K : ℕ) :
    ∃ K' : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Langlands.Analysis.schwartzVanishingOnKernel ℓ,
      schwartzSup ℂ K (Langlands.Analysis.schwartzLinearDivision ℓ hℓ f) ≤
        C * schwartzSup ℂ K' (f : 𝓢(X, ℂ)) := by
  let M := Langlands.Analysis.schwartzVanishingOnKernel ℓ
  have hp : WithSeminorms ((schwartzSeminormFamily ℂ X ℂ).comp M.subtype) :=
    LinearMap.withSeminorms_induced (schwartz_withSeminorms ℂ X ℂ) M.subtype
  obtain ⟨K', C, hC, hb⟩ := exists_schwartzSup_bound hp
    (Langlands.Analysis.schwartzLinearDivision ℓ hℓ) K
  refine ⟨K', C, hC, fun f => (hb f).trans_eq ?_⟩
  rw [← SeminormFamily.finset_sup_comp]
  rfl

/-- **Iterated division by linear forms.** Let `ℓ_j ≠ 0` for every `j ∈ s` and fix an output order
`K`. There are an order `K'` and a constant `C ≥ 0`, depending on the forms and on `K`, such that
whenever a Schwartz function `g` is the product of the imaginary linear factors `i ℓ_j(x)`,
`j ∈ s`, with a continuous function `h`, the function `h` is a Schwartz function `g'` with
`schwartzSup K g' ≤ C · schwartzSup K' g`. -/
theorem exists_iterated_division {ι : Type*} (l : ι → X →L[ℝ] ℝ) (s : Finset ι)
    (hl : ∀ i ∈ s, l i ≠ 0) (K : ℕ) :
    ∃ K' : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : 𝓢(X, ℂ)) (h : X → ℂ), Continuous h →
      (∀ x, g x = (∏ i ∈ s, Complex.I * (l i x : ℂ)) * h x) →
      ∃ g' : 𝓢(X, ℂ), (∀ x, g' x = h x) ∧ schwartzSup ℂ K g' ≤ C * schwartzSup ℂ K' g := by
  induction s using Finset.induction_on generalizing K with
  | empty =>
    refine ⟨K, 1, zero_le_one, fun g h _ hg => ⟨g, fun x => by simpa using hg x, by simp⟩⟩
  | @insert i s hi ih =>
    obtain ⟨K₁, C₁, hC₁, H₁⟩ := ih (fun j hj => hl j (Finset.mem_insert_of_mem hj)) K
    have hli : l i ≠ 0 := hl i (Finset.mem_insert_self i s)
    obtain ⟨K₂, C₂, hC₂, H₂⟩ := exists_division_bound (l i) hli K₁
    refine ⟨K₂, C₁ * C₂, mul_nonneg hC₁ hC₂, fun g h hh hg => ?_⟩
    have hgv : g ∈ Langlands.Analysis.schwartzVanishingOnKernel (l i) := by
      intro x hx
      rw [hg x, Finset.prod_insert hi, hx]
      simp
    let f : Langlands.Analysis.schwartzVanishingOnKernel (l i) := ⟨g, hgv⟩
    let g₁ : 𝓢(X, ℂ) := (-Complex.I) • Langlands.Analysis.schwartzLinearDivision (l i) hli f
    have hcont : Continuous (fun x => (∏ j ∈ s, Complex.I * (l j x : ℂ)) * h x) := by
      refine (continuous_finsetProd _ fun j _ => ?_).mul hh
      exact continuous_const.mul (Complex.continuous_ofReal.comp (l j).continuous)
    have hg₁ : ∀ x, g₁ x = (∏ j ∈ s, Complex.I * (l j x : ℂ)) * h x := by
      have heq := Continuous.ext_on (dense_nonzero_forms {()} (fun _ => l i) (by simp [hli]))
        g₁.continuous hcont (fun x hx => ?_)
      · exact fun x => congrFun heq x
      · have hx' : l i x ≠ 0 := hx () (Finset.mem_singleton_self _)
        have hdiv := Langlands.Analysis.smul_schwartzLinearDivision_apply (l i) hli f x
        change (l i x : ℝ) • Langlands.Analysis.schwartzLinearDivision (l i) hli f x = g x at hdiv
        rw [hg x, Finset.prod_insert hi, Complex.real_smul] at hdiv
        have hx'' : (l i x : ℂ) ≠ 0 := by exact_mod_cast hx'
        change -Complex.I * Langlands.Analysis.schwartzLinearDivision (l i) hli f x = _
        have hq : Langlands.Analysis.schwartzLinearDivision (l i) hli f x =
            Complex.I * ((∏ j ∈ s, Complex.I * (l j x : ℂ)) * h x) := by
          apply mul_left_cancel₀ hx''
          rw [hdiv]; ring
        rw [hq, ← mul_assoc, ← mul_assoc, show -Complex.I * Complex.I = 1 by
          rw [neg_mul, Complex.I_mul_I, neg_neg], one_mul]
    obtain ⟨g', hg', hb⟩ := H₁ g₁ h hh hg₁
    refine ⟨g', hg', hb.trans ?_⟩
    have hsm : schwartzSup ℂ K₁ g₁ =
        schwartzSup ℂ K₁ (Langlands.Analysis.schwartzLinearDivision (l i) hli f) := by
      simp only [g₁, map_smul_eq_mul, norm_neg, Complex.norm_I, one_mul]
    rw [hsm, mul_assoc]
    exact mul_le_mul_of_nonneg_left (H₂ f) hC₁

end Division

section Family

/-- A finite product of complex functions of temperate growth has temperate growth. -/
theorem hasTemperateGrowth_finset_prod {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {ι : Type*} (s : Finset ι) (f : ι → X → ℂ) (hf : ∀ i ∈ s, (f i).HasTemperateGrowth) :
    (fun x => ∏ i ∈ s, f i x).HasTemperateGrowth := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp_rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).fun_mul
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {R : Finset E} {a : Submodule ℝ E}

omit [FiniteDimensional ℝ E] in
/-- The imaginary linear factor `Λ ↦ i Λ(v)` has temperate growth. -/
theorem hasTemperateGrowth_imaginaryEval (v : a) :
    (fun Λ : StrongDual ℝ a => Complex.I * (Λ v : ℂ)).HasTemperateGrowth := by
  have h : (fun Λ : StrongDual ℝ a => Complex.I * (Λ v : ℂ)) =
      ⇑((Complex.I : ℂ) • (Complex.ofRealCLM.comp (ContinuousLinearMap.apply ℝ ℝ v)) :
        StrongDual ℝ a →L[ℝ] ℂ) := by
    ext Λ
    simp
  rw [h]
  exact ContinuousLinearMap.hasTemperateGrowth _

theorem theta_hasTemperateGrowth (S : Finset E) :
    (theta a S).HasTemperateGrowth := by
  have h : theta a S = fun Λ => ((gramVolume fun v : simpleRoots a S => ((v : a) : E) : ℝ) : ℂ)⁻¹ *
      ∏ v : simpleRoots a S, (Complex.I * (Λ (v : a) : ℂ)) := rfl
  rw [h]
  exact (Function.HasTemperateGrowth.const _).fun_mul
    (hasTemperateGrowth_finset_prod _ _ fun v _ => hasTemperateGrowth_imaginaryEval (v : a))

/-- **Lapid's Corollary 3, with bounds.** Fix an output order `K`. There are an order `K'` and a
constant `C ≥ 0`, depending on the root set, the Levi space and `K`, such that for every
`(G, M)`-family `d` of Schwartz functions there is a Schwartz function `F` that equals the weighted
sum `c_M` of `d` wherever all `θ_S` are nonzero and satisfies
`schwartzSup K F ≤ C · ∑_S schwartzSup K' (d S)`. -/
theorem exists_schwartz_cM (hR : IsRootSet R) (ha : IsLeviSpace R a) (K : ℕ) :
    ∃ K' : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ d : Finset E → 𝓢(StrongDual ℝ a, ℂ),
      IsFamily R a (fun S Λ => d S Λ) →
      ∃ F : 𝓢(StrongDual ℝ a, ℂ),
        (∀ Λ, (∀ S ∈ parabolics R a, theta a S Λ ≠ 0) →
          F Λ = cM R a (fun S Λ => d S Λ) Λ) ∧
        schwartzSup ℂ K F ≤ C * ∑ S ∈ parabolics R a, schwartzSup ℂ K' (d S) := by
  let 𝓟 := parabolics R a
  let ι := Σ S : 𝓟, simpleRoots a (S : Finset E)
  let l : ι → StrongDual ℝ a →L[ℝ] ℝ := fun σ => ContinuousLinearMap.apply ℝ ℝ ((σ.2 : a))
  have hl : ∀ σ ∈ (Finset.univ : Finset ι), l σ ≠ 0 := by
    intro σ _ hz
    have hne := (linearIndependent_simpleRoots hR ha σ.1.2).ne_zero σ.2
    obtain ⟨Λ, hΛ⟩ : ∃ Λ : StrongDual ℝ a, Λ (σ.2 : a) ≠ 0 :=
      ⟨innerSL ℝ (σ.2 : a), by
        rw [innerSL_apply_apply]
        exact (real_inner_self_pos.mpr hne).ne'⟩
    exact hΛ (by simpa [l] using congrArg (fun T => T Λ) hz)
  let gv (S : Finset E) : ℝ := gramVolume fun v : simpleRoots a S => ((v : a) : E)
  have hgv (S : Finset E) (hS : S ∈ 𝓟) : gv S ≠ 0 := by
    have hli : LinearIndependent ℝ (fun v : simpleRoots a S => ((v : a) : E)) :=
      (linearIndependent_simpleRoots hR ha hS).map' a.subtype
        (LinearMap.ker_eq_bot.mpr a.injective_subtype)
    exact ((gramVolume_pos_iff _).mpr hli).ne'
  let C₀ : ℂ := ∏ S ∈ 𝓟, ((gv S : ℝ) : ℂ)⁻¹
  have hC₀ : C₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun S hS =>
    inv_ne_zero (by exact_mod_cast hgv S hS)
  have hΘ (Λ : StrongDual ℝ a) : ∏ S ∈ 𝓟, theta a S Λ =
      C₀ * ∏ σ ∈ (Finset.univ : Finset ι), Complex.I * (l σ Λ : ℂ) := by
    have h1 : ∏ S ∈ 𝓟, theta a S Λ = ∏ S : 𝓟, theta a (S : Finset E) Λ :=
      (Finset.prod_coe_sort 𝓟 _).symm
    have h2 : ∏ σ ∈ (Finset.univ : Finset ι), Complex.I * (l σ Λ : ℂ) =
        ∏ S : 𝓟, ∏ v : simpleRoots a (S : Finset E), Complex.I * (Λ (v : a) : ℂ) := by
      rw [← Finset.univ_sigma_univ, Finset.prod_sigma]
      rfl
    have h3 : C₀ = ∏ S : 𝓟, ((gv (S : Finset E) : ℝ) : ℂ)⁻¹ :=
      (Finset.prod_coe_sort 𝓟 _).symm
    rw [h1, h2, h3, ← Finset.prod_mul_distrib]
    rfl
  -- the multipliers `π_S = ∏_{S' ≠ S} θ_{S'}`
  let π (S : Finset E) (Λ : StrongDual ℝ a) : ℂ := ∏ S' ∈ 𝓟.erase S, theta a S' Λ
  have hπ (S : Finset E) : (π S).HasTemperateGrowth :=
    hasTemperateGrowth_finset_prod _ _ fun S' _ => theta_hasTemperateGrowth S'
  obtain ⟨K₁, C₁, hC₁, H₁⟩ := exists_iterated_division (X := StrongDual ℝ a) l Finset.univ
    (fun σ hσ => hl σ hσ) K
  have hmul (S : Finset E) : ∃ K₂ : ℕ, ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ f : 𝓢(StrongDual ℝ a, ℂ),
      schwartzSup ℂ K₁ (SchwartzMap.smulLeftCLM ℂ (π S) f) ≤ C₂ * schwartzSup ℂ K₂ f :=
    exists_schwartzSup_bound_schwartz (SchwartzMap.smulLeftCLM ℂ (π S)) K₁
  choose K₂ C₂ hC₂ H₂ using hmul
  refine ⟨𝓟.sup K₂, ‖C₀⁻¹‖ * C₁ * ∑ S ∈ 𝓟, C₂ S,
    mul_nonneg (mul_nonneg (norm_nonneg _) hC₁) (Finset.sum_nonneg fun S _ => hC₂ S),
    fun d hd => ?_⟩
  obtain ⟨F₀, hF₀, hF₀e⟩ := smoothExtension R a hR ha (fun S Λ => d S Λ) hd
  let N : 𝓢(StrongDual ℝ a, ℂ) := ∑ S ∈ 𝓟, SchwartzMap.smulLeftCLM ℂ (π S) (d S)
  have hNapply (Λ : StrongDual ℝ a) : N Λ = ∑ S ∈ 𝓟, π S Λ * d S Λ := by
    simp only [N, SchwartzMap.sum_apply, SchwartzMap.smulLeftCLM_apply_apply (hπ _), smul_eq_mul]
  have hhcont : Continuous (fun Λ => C₀ * F₀ Λ) := continuous_const.mul hF₀.continuous
  have hNeq : ∀ Λ, N Λ = (∏ σ ∈ (Finset.univ : Finset ι), Complex.I * (l σ Λ : ℂ)) *
      (C₀ * F₀ Λ) := by
    have hcont : Continuous (fun Λ => (∏ σ ∈ (Finset.univ : Finset ι),
        Complex.I * (l σ Λ : ℂ)) * (C₀ * F₀ Λ)) := by
      refine (continuous_finsetProd _ fun σ _ => ?_).mul hhcont
      exact continuous_const.mul (Complex.continuous_ofReal.comp (l σ).continuous)
    have heq := Continuous.ext_on (dense_nonzero_forms Finset.univ l hl) N.continuous hcont
      (fun Λ hΛ => ?_)
    · exact fun Λ => congrFun heq Λ
    · have hθ : ∀ S ∈ 𝓟, theta a S Λ ≠ 0 := by
        intro S hS
        refine mul_ne_zero (inv_ne_zero (by exact_mod_cast hgv S hS))
          (Finset.prod_ne_zero_iff.mpr fun v _ => mul_ne_zero Complex.I_ne_zero ?_)
        exact_mod_cast hΛ ⟨⟨S, hS⟩, v⟩ (Finset.mem_univ _)
      change N Λ = (∏ σ ∈ (Finset.univ : Finset ι), Complex.I * (l σ Λ : ℂ)) * (C₀ * F₀ Λ)
      rw [hF₀e Λ hθ, hNapply, ← mul_assoc, mul_comm _ C₀, ← hΘ, cM, Finset.mul_sum]
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [← Finset.mul_prod_erase 𝓟 (fun S' => theta a S' Λ) hS]
      change π S Λ * d S Λ = theta a S Λ * π S Λ * (d S Λ * (theta a S Λ)⁻¹)
      field_simp [hθ S hS]
  obtain ⟨g', hg', hgb⟩ := H₁ N (fun Λ => C₀ * F₀ Λ) hhcont hNeq
  refine ⟨C₀⁻¹ • g', fun Λ hΛ => ?_, ?_⟩
  · rw [SchwartzMap.smul_apply, hg', smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hC₀, one_mul,
      hF₀e Λ hΛ]
  · have hN : schwartzSup ℂ K₁ N ≤ ∑ S ∈ 𝓟, C₂ S * schwartzSup ℂ (𝓟.sup K₂) (d S) := by
      refine (Finset.le_sum_of_subadditive (schwartzSup ℂ K₁) (map_zero _).le
        (map_add_le_add _) _ _).trans (Finset.sum_le_sum fun S hS => ?_)
      exact (H₂ S (d S)).trans (mul_le_mul_of_nonneg_left
        (schwartzSup_mono (Finset.le_sup hS) _) (hC₂ S))
    have hsum : ∑ S ∈ 𝓟, C₂ S * schwartzSup ℂ (𝓟.sup K₂) (d S) ≤
        (∑ S ∈ 𝓟, C₂ S) * ∑ S ∈ 𝓟, schwartzSup ℂ (𝓟.sup K₂) (d S) := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_le_sum fun S hS => ?_
      exact Finset.single_le_sum (f := fun S' => C₂ S * schwartzSup ℂ (𝓟.sup K₂) (d S'))
        (fun S' _ => mul_nonneg (hC₂ S) (apply_nonneg _ _)) hS
    calc schwartzSup ℂ K (C₀⁻¹ • g') = ‖C₀⁻¹‖ * schwartzSup ℂ K g' := map_smul_eq_mul _ _ _
      _ ≤ ‖C₀⁻¹‖ * (C₁ * schwartzSup ℂ K₁ N) := mul_le_mul_of_nonneg_left hgb (norm_nonneg _)
      _ ≤ ‖C₀⁻¹‖ * (C₁ * ((∑ S ∈ 𝓟, C₂ S) * ∑ S ∈ 𝓟, schwartzSup ℂ (𝓟.sup K₂) (d S))) := by
        gcongr
        exact hN.trans hsum
      _ = _ := by ring

end Family

end Langlands.GMFamily
