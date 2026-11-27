import Langlands.LinearAlgebra.GMFamilyOrthogonalSetBounds

/-! # Proof of Lapid's Lemma 8 for positive orthogonal sets

`Langlands.GMFamily.orthogonalSetLimit` proves `Langlands.GMFamily.OrthogonalSetLimitStatement`. -/

noncomputable section

open scoped RealInnerProductSpace SchwartzMap Topology
open Finset Classical MeasureTheory Complex
open Langlands.Analysis

universe u

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {R : Finset E} {a : Submodule ℝ E}

theorem cQM_empty (c : Finset E → StrongDual ℝ a → ℂ) (Λ : StrongDual ℝ a) :
    cQM R a c ∅ Λ = cM R a c Λ := by
  unfold cQM cM
  rw [leviRoots_empty]
  simp only [Finset.empty_union]

/-- For a fixed positive orthogonal set `Y` and a face `Q = posSet R w`, `c_M^Q(Λ_x)` of the exponential
family `e^{λ(Y_S)}` is bounded, by a constant depending on `Y`, at the points `x ∈ 𝔞_M^G` with
`Λ_x` off the walls. (The point `ξ` off the walls serves as the direction of the uniform bound
`norm_expShift_le`.) -/
theorem exists_norm_cQM_exp_le (hR : IsRootSet R) (ha : IsLeviSpace R a) (w : a)
    {Y : Finset E → a} (hY : IsPositiveOrthogonalSet R a Y) (ξ : relativeSpace R a)
    (hξ : OffWalls R a (dualParam R a ξ)) :
    ∃ K : ℝ, ∀ x : relativeSpace R a, OffWalls R a (dualParam R a x) →
      ‖cQM R a (fun S Λ => exp (I * (Λ (Y S) : ℂ))) (posSet R (w : E)) (dualParam R a x)‖ ≤ K := by
  let R' := leviRoots R (posSet R (w : E))
  have hR' : IsRootSet R' := isRootSet_leviRoots_posSet hR _
  have ha' : IsLeviSpace R' a := isLeviSpace_leviRoots ha w
  have hsub : R' ⊆ R := Finset.filter_subset _ _
  let y : Finset E → a := fun S => Y (posSet R (w : E) ∪ S)
  have hy := isFamily_face hR w (isFamily_exp_of_orthogonal hY)
  refine ⟨expShiftBound R' a y (dualParam R a ξ), fun x hx => ?_⟩
  have h := norm_expShift_le hR' ha' y hy (dualParam R a ξ)
    (fun S hS v hv => apply_simpleRoot_ne_zero_of_offWalls hR' ha' hsub hS hξ hv)
    (dualParam R a x) (s := 0) (by simp) (by simp) (fun S hS v hv => by
      rw [zero_mul, add_zero]
      exact_mod_cast apply_simpleRoot_ne_zero_of_offWalls hR' ha' hsub hS hx hv)
  rw [expShift_zero] at h
  exact h

variable [MeasurableSpace E] [BorelSpace E]

theorem measurable_cQM_dualParam {c : Finset E → StrongDual ℝ a → ℂ}
    (hc : ∀ S, Continuous (c S)) (Q : Finset E) :
    Measurable (fun x : relativeSpace R a => cQM R a c Q (dualParam R a x)) := by
  unfold cQM
  refine Finset.measurable_sum _ fun S _ => ?_
  exact ((hc _).comp continuous_dualParam).measurable.mul
    (((theta_hasTemperateGrowth (a := a) S).1.continuous.comp continuous_dualParam).measurable.inv)

/-- **The estimate at a fixed chamber.** For a chamber `S₀` and `n ∈ ℕ` there are `K` and `C ≥ 0`
such that for every `(G, M)`-family `d` of Schwartz functions, every `t ≥ 0` and every positive
`(G, M)`-orthogonal set `Y` with `⟪v, Y_S⟫ ≥ t` for all chambers `S` and simple roots `v`,
`|(2π)^{−k} ∫ (cd)_M(Λ_x) dx − d_{S₀}(0)| ≤ C (∑_P schwartzSup K (d_P)) (1 + t)^{−n}`, where
`(cd)_M` is `c_M` of the family `e^{λ(Y_S)} d_S(λ)` and `k = dim 𝔞_M^G`. -/
theorem exists_bound_at_chamber (hR : IsRootSet R) (ha : IsLeviSpace R a) {S₀ : Finset E}
    (hS₀ : S₀ ∈ parabolics R a) (n : ℕ) :
    ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ d : Finset E → 𝓢(StrongDual ℝ a, ℂ),
      IsFamily R a (fun S Λ => d S Λ) →
      ∀ (Y : Finset E → a) (t : ℝ), 0 ≤ t → IsPositiveOrthogonalSet R a Y →
        (∀ S ∈ parabolics R a, ∀ v ∈ simpleRoots a S, t ≤ ⟪v, Y S⟫) →
          ‖((((2 * Real.pi) ^ Module.finrank ℝ (relativeSpace R a))⁻¹ : ℝ) : ℂ) *
              (∫ x : relativeSpace R a,
                cM R a (fun S Λ => exp (I * (Λ (Y S) : ℂ)) * d S Λ) (dualParam R a x))
            - d S₀ 0‖ ≤
            C * (∑ P ∈ parabolics R a, schwartzSup ℂ K (d P)) * ((1 + t) ^ n)⁻¹ := by
  obtain ⟨ξ, hreg, hsec, hgen⟩ := exists_generic_displacement hR ha hS₀
  have hξ : OffWalls R a (dualParam R a ξ) := (offWalls_dualParam_iff ξ).mpr fun α hα hne => by
    rw [real_inner_comm]; exact hgen α hα hne
  let V := relativeSpace R a
  let k := Module.finrank ℝ V
  let N := n + k + 1
  let T := leviSpaces R a ×ˢ leviSpaces R a
  have hface : ∀ L : Submodule ℝ E × Submodule ℝ E, ∃ w₁ w₂ : a, L ∈ T →
      (splittingSection R (ξ : E) L.1 L.2).1 = posSet R (w₁ : E) ∧
        (splittingSection R (ξ : E) L.1 L.2).2 = posSet R (w₂ : E) := by
    intro L
    by_cases hL : L ∈ T
    · obtain ⟨hL₁, hL₂⟩ := Finset.mem_product.mp hL
      obtain ⟨w₁, h₁⟩ := splittingSection_fst_face (R := R) (ξ := (ξ : E)) (L₂ := L.2)
        ((mem_leviSpaces_iff hR ha _).mp hL₁).1
      obtain ⟨w₂, h₂⟩ := splittingSection_snd_face (R := R) (ξ := (ξ : E)) (L₁ := L.1)
        ((mem_leviSpaces_iff hR ha _).mp hL₂).1
      exact ⟨w₁, w₂, fun _ => ⟨h₁, h₂⟩⟩
    · exact ⟨0, 0, fun h => (hL h).elim⟩
  choose w₁ w₂ hw using hface
  have hdside : ∀ L : Submodule ℝ E × Submodule ℝ E, ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ d : Finset E → 𝓢(StrongDual ℝ a, ℂ), IsFamily R a (fun S Λ => d S Λ) →
      ∃ u : 𝓢(V, ℂ),
        (∀ x : V, OffWalls R a (dualParam R a x) →
          u x = cQM R a (fun S Λ => d S Λ) (posSet R (w₂ L : E)) (dualParam R a x)) ∧
        ∀ H : V, (1 + ‖H‖) ^ N * ‖phaseFourier u H‖ ≤
          C * ∑ P ∈ parabolics R a, schwartzSup ℂ K (d P) :=
    fun L => exists_face_schwartz hR ha (w₂ L) N
  choose Kd Cd hCd hdu using hdside
  have heside : ∀ L : Submodule ℝ E × Submodule ℝ E, ∃ C : ℝ, 0 ≤ C ∧
      (posSet R (w₁ L : E) ≠ ∅ → ∀ (Y : Finset E → a) (t : ℝ), 0 ≤ t →
        IsPositiveOrthogonalSet R a Y →
        (∀ S ∈ parabolics R a, ∀ v ∈ simpleRoots a S, t ≤ ⟪v, Y S⟫) →
        ∀ (u : 𝓢(V, ℂ)) (A : ℝ), (∀ H, (1 + ‖H‖) ^ N * ‖phaseFourier u H‖ ≤ A) →
          ‖∫ x : V, cQM R a (fun S Λ => exp (I * (Λ (Y S) : ℂ))) (posSet R (w₁ L : E))
            (dualParam R a x) * u x‖ ≤ C * A * ((1 + t) ^ n)⁻¹) := by
    intro L
    by_cases h : posSet R (w₁ L : E) = ∅
    · exact ⟨0, le_rfl, fun h' => (h' h).elim⟩
    · obtain ⟨C, hC, hb⟩ := exists_face_term_bound hR ha (w₁ L) h ξ hξ n
      exact ⟨C, hC, fun _ => hb⟩
  choose Ce hCe heb using heside
  obtain ⟨Cm, hCm, hmain⟩ := exists_main_term_bound hR ha ξ hξ n
  let Lstar : Submodule ℝ E × Submodule ℝ E := (centralSpace R, a)
  have hLstar : Lstar ∈ T :=
    Finset.mem_product.mpr ⟨centralSpace_mem_leviSpaces hR ha, self_mem_leviSpaces hR ha⟩
  refine ⟨T.sup Kd, Cm * Cd Lstar + ∑ L ∈ T, |dCoeff R a L.1 L.2| * (Ce L * Cd L),
    add_nonneg (mul_nonneg hCm (hCd _)) (Finset.sum_nonneg fun L _ =>
      mul_nonneg (abs_nonneg _) (mul_nonneg (hCe L) (hCd L))),
    fun d hd Y t ht hY hYt => ?_⟩
  let c : Finset E → StrongDual ℝ a → ℂ := fun S Λ => exp (I * (Λ (Y S) : ℂ))
  have hc : IsFamily R a c := isFamily_exp_of_orthogonal hY
  have hcc : ∀ S, Continuous (c S) := fun S =>
    (Complex.contDiff_exp.comp (hasTemperateGrowth_imaginaryEval (Y S)).1).continuous
  have hdc : ∀ S, Continuous (fun Λ : StrongDual ℝ a => d S Λ) := fun S => (d S).continuous
  choose u hu_eq hu_dec using fun L => hdu L d hd
  let B : ℝ := ∑ P ∈ parabolics R a, schwartzSup ℂ (T.sup Kd) (d P)
  let A (L : Submodule ℝ E × Submodule ℝ E) : ℝ :=
    Cd L * ∑ P ∈ parabolics R a, schwartzSup ℂ (Kd L) (d P)
  have hAB : ∀ L ∈ T, A L ≤ Cd L * B := fun L hL =>
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun P _ =>
      schwartzSup_mono (Finset.le_sup hL) _) (hCd L)
  have hB : 0 ≤ B := Finset.sum_nonneg fun P _ => apply_nonneg _ _
  set r : ℝ := ((1 + t) ^ n)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  -- the terms
  let J (L : Submodule ℝ E × Submodule ℝ E) : ℂ :=
    ∫ x : V, cQM R a c (posSet R (w₁ L : E)) (dualParam R a x) * u L x
  have hint : ∀ L, Integrable (fun x : V => cQM R a c (posSet R (w₁ L : E)) (dualParam R a x) *
      u L x) := by
    intro L
    obtain ⟨K', hK'⟩ := exists_norm_cQM_exp_le hR ha (w₁ L) hY ξ hξ
    exact (u L).integrable.bdd_mul (measurable_cQM_dualParam hcc _).aestronglyMeasurable
      ((ae_offWalls ha).mono fun x hx => hK' x hx)
  -- the alternate splitting formula almost everywhere
  have hae : (fun x : V => cM R a (fun S Λ => exp (I * (Λ (Y S) : ℂ)) * d S Λ) (dualParam R a x))
      =ᵐ[volume] fun x => ∑ L ∈ T, (dCoeff R a L.1 L.2 : ℂ) *
        (cQM R a c (posSet R (w₁ L : E)) (dualParam R a x) * u L x) := by
    filter_upwards [ae_offWalls ha] with x hx
    have h : cM R a (familyMul a c (fun S Λ => d S Λ)) (dualParam R a x) =
        ∑ L₁ ∈ leviSpaces R a, ∑ L₂ ∈ leviSpaces R a, (dCoeff R a L₁ L₂ : ℂ) *
          cQM R a c (splittingSection R (ξ : E) L₁ L₂).1 (dualParam R a x) *
            cQM R a (fun S Λ => d S Λ) (splittingSection R (ξ : E) L₁ L₂).2 (dualParam R a x) :=
      alternateSplitting_of_offWalls hR ha hc hd hcc hdc ξ hreg (y := ⟨x, x.property.1⟩) hx
    change cM R a (familyMul a c (fun S Λ => d S Λ)) (dualParam R a x) = _
    rw [h, ← Finset.sum_product' (leviSpaces R a) (leviSpaces R a)]
    refine Finset.sum_congr rfl fun L hL => ?_
    obtain ⟨h1, h2⟩ := hw L hL
    rw [h1, h2, hu_eq L x hx]
    ring
  have hJsum : ∫ x : V, cM R a (fun S Λ => exp (I * (Λ (Y S) : ℂ)) * d S Λ) (dualParam R a x) =
      ∑ L ∈ T, (dCoeff R a L.1 L.2 : ℂ) * J L := by
    rw [integral_congr_ae hae, integral_finsetSum _ fun L _ => (hint L).const_mul _]
    exact Finset.sum_congr rfl fun L _ => integral_const_mul _ _
  -- the main pair
  have hsecstar := splittingSection_centralSpace_self (R := R) ξ
  have hw₁star : posSet R (w₁ Lstar : E) = ∅ := by
    rw [← (hw Lstar hLstar).1]
    exact congrArg Prod.fst hsecstar
  have hw₂star : posSet R (w₂ Lstar : E) = S₀ := by
    rw [← (hw Lstar hLstar).2, ← hsec]
    exact congrArg Prod.snd hsecstar
  have hustar : ∀ x : V, u Lstar x = d S₀ (dualParam R a x) := by
    have hae' : (fun x : V => u Lstar x) =ᵐ[volume] fun x => d S₀ (dualParam R a x) := by
      filter_upwards [ae_offWalls ha] with x hx
      rw [hu_eq Lstar x hx, hw₂star, cQM_parabolic hR hS₀]
    have := (Continuous.ae_eq_iff_eq volume (u Lstar).continuous
      ((d S₀).continuous.comp continuous_dualParam)).mp hae'
    exact fun x => congrFun this x
  have hu0 : u Lstar 0 = d S₀ 0 := by rw [hustar, dualParam_zero]
  have hJstar : J Lstar = ∫ x : V, cM R a c (dualParam R a x) * u Lstar x := by
    simp only [J, hw₁star, cQM_empty]
  have hmainb := hmain Y t ht hY hYt (u Lstar) (A Lstar) (hu_dec Lstar)
  rw [← hJstar, hu0] at hmainb
  -- the other pairs
  have hothers : ∀ L ∈ T.erase Lstar, ‖(dCoeff R a L.1 L.2 : ℂ) * J L‖ ≤
      |dCoeff R a L.1 L.2| * (Ce L * (Cd L * B) * r) := by
    intro L hL
    obtain ⟨hne, hLT⟩ := Finset.mem_erase.mp hL
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hd0 : dCoeff R a L.1 L.2 = 0
    · rw [hd0, abs_zero, zero_mul, zero_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hQ : posSet R (w₁ L : E) ≠ ∅ := by
      intro hQ
      obtain ⟨hL₁, hL₂⟩ := Finset.mem_product.mp hLT
      have h1 := (hw L hLT).1
      rw [hQ] at h1
      obtain ⟨e1, e2⟩ := eq_centralSpace_self_of_section_empty hR ha hL₁ hL₂ hd0 ξ hreg h1
      exact hne (Prod.ext e1 e2)
    refine (heb L hQ Y t ht hY hYt (u L) (A L) (hu_dec L)).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hAB L hLT) (hCe L)) hr0
  -- assembly
  set κ : ℝ := ((2 * Real.pi) ^ k)⁻¹ with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hκ1 : κ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [Real.two_le_pi]))
  have hdstar : dCoeff R a Lstar.1 Lstar.2 = 1 := dCoeff_centralSpace_self
  rw [hJsum, ← Finset.add_sum_erase T _ hLstar, hdstar, Complex.ofReal_one, one_mul, mul_add]
  have hsplit : (κ : ℂ) * J Lstar + (κ : ℂ) * ∑ L ∈ T.erase Lstar, (dCoeff R a L.1 L.2 : ℂ) * J L -
      d S₀ 0 = ((κ : ℂ) * J Lstar - d S₀ 0) +
        (κ : ℂ) * ∑ L ∈ T.erase Lstar, (dCoeff R a L.1 L.2 : ℂ) * J L := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h2 : ‖(κ : ℂ) * ∑ L ∈ T.erase Lstar, (dCoeff R a L.1 L.2 : ℂ) * J L‖ ≤
      ∑ L ∈ T, |dCoeff R a L.1 L.2| * (Ce L * (Cd L * B) * r) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ0]
    calc κ * ‖∑ L ∈ T.erase Lstar, (dCoeff R a L.1 L.2 : ℂ) * J L‖
        ≤ 1 * ∑ L ∈ T.erase Lstar, |dCoeff R a L.1 L.2| * (Ce L * (Cd L * B) * r) :=
          mul_le_mul hκ1 ((norm_sum_le _ _).trans (Finset.sum_le_sum hothers)) (norm_nonneg _)
            zero_le_one
      _ ≤ ∑ L ∈ T, |dCoeff R a L.1 L.2| * (Ce L * (Cd L * B) * r) := by
          rw [one_mul]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun L _ _ =>
            mul_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg (hCe L)
              (mul_nonneg (hCd L) hB)) hr0)
  have h1 : ‖(κ : ℂ) * J Lstar - d S₀ 0‖ ≤ Cm * (Cd Lstar * B) * r :=
    hmainb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (hAB Lstar hLstar) hCm) hr0)
  calc _ ≤ Cm * (Cd Lstar * B) * r + ∑ L ∈ T, |dCoeff R a L.1 L.2| * (Ce L * (Cd L * B) * r) :=
        add_le_add h1 h2
    _ = (Cm * Cd Lstar + ∑ L ∈ T, |dCoeff R a L.1 L.2| * (Ce L * Cd L)) * B * r := by
        rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun L _ => by ring

/-- **Lapid's Lemma 8** for positive orthogonal sets: the proof of
`Langlands.GMFamily.OrthogonalSetLimitStatement`. -/
theorem orthogonalSetLimit : OrthogonalSetLimitStatement.{u} := by
  intro E _ _ _ _ _ R a hR ha n κ
  have h : ∀ S₀ : Finset E, ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (S₀ ∈ parabolics R a →
      ∀ d : Finset E → 𝓢(StrongDual ℝ a, ℂ), IsFamily R a (fun S Λ => d S Λ) →
      ∀ (Y : Finset E → a) (t : ℝ), 0 ≤ t → IsPositiveOrthogonalSet R a Y →
        (∀ S ∈ parabolics R a, ∀ v ∈ simpleRoots a S, t ≤ ⟪v, Y S⟫) →
          ‖((((2 * Real.pi) ^ Module.finrank ℝ (relativeSpace R a))⁻¹ : ℝ) : ℂ) *
              (∫ x : relativeSpace R a,
                cM R a (fun S Λ => exp (I * (Λ (Y S) : ℂ)) * d S Λ) (dualParam R a x))
            - d S₀ 0‖ ≤
            C * (∑ P ∈ parabolics R a, schwartzSup ℂ K (d P)) * ((1 + t) ^ n)⁻¹) := by
    intro S₀
    by_cases hS₀ : S₀ ∈ parabolics R a
    · obtain ⟨K, C, hC, hb⟩ := exists_bound_at_chamber hR ha hS₀ n
      exact ⟨K, C, hC, fun _ => hb⟩
    · exact ⟨0, 0, le_rfl, fun h => (hS₀ h).elim⟩
  choose K C hC hb using h
  refine ⟨Finset.Iic ((parabolics R a).sup K, (parabolics R a).sup K),
    ∑ S ∈ parabolics R a, C S, fun d hd Y t ht hY hYt _ S₀ hS₀ => ?_⟩
  refine (hb S₀ hS₀ d hd Y t ht hY hYt).trans ?_
  have hsum : ∑ P ∈ parabolics R a, schwartzSup ℂ (K S₀) (d P) ≤
      ∑ S ∈ parabolics R a, (Finset.Iic ((parabolics R a).sup K, (parabolics R a).sup K)).sup
        (schwartzSeminormFamily ℝ (StrongDual ℝ a) ℂ) (d S) :=
    Finset.sum_le_sum fun S _ => by
      rw [← schwartzSup_real_eq (𝕜 := ℂ)]
      exact schwartzSup_mono (Finset.le_sup hS₀) _
  have hC₀ : C S₀ ≤ ∑ S ∈ parabolics R a, C S :=
    Finset.single_le_sum (fun S _ => hC S) hS₀
  have hr : 0 ≤ ((1 + t) ^ n)⁻¹ := by positivity
  have hX : 0 ≤ ∑ P ∈ parabolics R a, schwartzSup ℂ (K S₀) (d P) :=
    Finset.sum_nonneg fun P _ => apply_nonneg _ _
  rw [div_eq_mul_inv]
  calc _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul hC₀ hsum hX
        (Finset.sum_nonneg fun S _ => hC S)) hr
    _ = _ := by ring

end Langlands.GMFamily
