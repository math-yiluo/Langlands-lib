import Langlands.LinearAlgebra.GMFamilyOrthogonalSetTerms

/-! # Bounds for the terms of the alternate splitting formula

Fix `ξ ∈ 𝔞_M^G` with `Λ_ξ` off the walls and `n ∈ ℕ`. Let `t ≥ 0`, let `Y` be a positive
`(G, M)`-orthogonal set with `⟪v, Y_P⟫ ≥ t` for all chambers `P` and simple roots `v`, and let `u`
be a Schwartz function on `𝔞_M^G` with `(1 + ‖H‖)^{n + k + 1} |phaseFourier u H| ≤ A`,
`k = dim 𝔞_M^G`. Then the integral of `c_M^{Q}(Λ_x, Y) u(x)` over `𝔞_M^G` is at most
`C A (1 + t)^{-n}` for every nonempty face `Q` (a parabolic subgroup `Q ≠ G`), and `(2π)^{-k}`
times the integral of `c_M(Λ_x, Y) u(x)` differs from `u(0)` by at most `C A (1 + t)^{-n}`; the
constants `C` do not depend on `Y`, `t`, `u` or `A`. -/

noncomputable section

open scoped RealInnerProductSpace SchwartzMap Topology
open Finset Classical MeasureTheory Complex
open Langlands.Analysis

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {R : Finset E} {a : Submodule ℝ E}

/-- The exponential family of a positive orthogonal set is a `(G, M)`-family. -/
theorem isFamily_exp_of_orthogonal {Y : Finset E → a} (hY : IsPositiveOrthogonalSet R a Y) :
    IsFamily R a (fun S Λ => exp (I * (Λ (Y S) : ℂ))) := by
  refine ⟨fun S _ => Complex.contDiff_exp.comp (hasTemperateGrowth_imaginaryEval (Y S)).1,
    fun S hS S' hS' v hadj Λ hΛ => ?_⟩
  obtain ⟨r, -, hr⟩ := hY S hS S' hS' v hadj
  have h : Λ (Y S) = Λ (Y S') := by
    have : Λ (Y S - Y S') = 0 := by rw [hr, map_smul, hΛ, smul_zero]
    rw [map_sub] at this
    linarith
  show exp (I * (Λ (Y S) : ℂ)) = exp (I * (Λ (Y S') : ℂ))
  rw [h]

theorem orthant_point_eq (hR : IsRootSet R) (ha : IsLeviSpace R a) {P : Finset E}
    (hP : P ∈ parabolics R a) {T : Finset a} (hT : T ⊆ simpleRoots a P) (Y : E) (X : T → ℝ) :
    (relativeSpace R a).orthogonalProjectionOnto (Y - ∑ v : T, X v • ((v : a) : E)) =
      (relativeSpace R a).orthogonalProjectionOnto Y -
        ∑ v : T, X v • chamberBasis hR ha hP ⟨v, hT v.property⟩ := by
  rw [map_sub, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_smul]
  congr 1
  have hb : ((chamberBasis hR ha hP ⟨v, hT v.property⟩ : relativeSpace R a) : E) = ((v : a) : E) :=
    chamberBasis_apply hR ha hP _
  rw [← hb, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem inner_simpleRoot_projection (hR : IsRootSet R) (ha : IsLeviSpace R a) {P : Finset E}
    (hP : P ∈ parabolics R a) (β : simpleRoots a P) (Y : E) :
    ⟪((β : a) : E), (((relativeSpace R a).orthogonalProjectionOnto Y : relativeSpace R a) : E)⟫ =
      ⟪((β : a) : E), Y⟫ := by
  have hb : ((chamberBasis hR ha hP β : relativeSpace R a) : E) = ((β : a) : E) :=
    chamberBasis_apply hR ha hP β
  rw [← hb]
  exact inner_relative_projection _ Y

theorem orthantSign_abs {ι : Type*} [Fintype ι] (d : ι → ℝ) : ‖orthantSign d‖ = 1 := by
  rw [orthantSign, norm_prod]
  exact Finset.prod_eq_one fun i _ => by split_ifs <;> simp

variable [MeasurableSpace E] [BorelSpace E]

/-- **The terms of proper faces decay.** For a nonempty face `Q = posSet R w`, `w ∈ a`, a point
`ξ ∈ 𝔞_M^G` with `Λ_ξ` off the walls and `n ∈ ℕ`, there is `C ≥ 0` such that for every `t ≥ 0`,
every positive `(G, M)`-orthogonal set `Y` with `⟪v, Y_S⟫ ≥ t` for all chambers `S` and simple roots
`v`, and every Schwartz `u` with `(1 + ‖H‖)^{n + dim 𝔞_M^G + 1} |phaseFourier u H| ≤ A`,
`|∫ c_M^Q(Λ_x) u(x) dx| ≤ C A (1 + t)^{−n}`, `c_M^Q` for the exponential family `e^{λ(Y_S)}`. -/
theorem exists_face_term_bound (hR : IsRootSet R) (ha : IsLeviSpace R a) (w : a)
    (hQ : posSet R (w : E) ≠ ∅) (ξ : relativeSpace R a) (hξ : OffWalls R a (dualParam R a ξ))
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y : Finset E → a) (t : ℝ), 0 ≤ t → IsPositiveOrthogonalSet R a Y →
      (∀ S ∈ parabolics R a, ∀ v ∈ simpleRoots a S, t ≤ ⟪v, Y S⟫) →
      ∀ (u : 𝓢(relativeSpace R a, ℂ)) (A : ℝ),
        (∀ H, (1 + ‖H‖) ^ (n + Module.finrank ℝ (relativeSpace R a) + 1) *
          ‖phaseFourier u H‖ ≤ A) →
        ‖∫ x : relativeSpace R a, cQM R a (fun S Λ => exp (I * (Λ (Y S) : ℂ)))
          (posSet R (w : E)) (dualParam R a x) * u x‖ ≤ C * A * ((1 + t) ^ n)⁻¹ := by
  let Q := posSet R (w : E)
  let R' := leviRoots R Q
  have hR' : IsRootSet R' := isRootSet_leviRoots_posSet hR _
  have ha' : IsLeviSpace R' a := isLeviSpace_leviRoots ha w
  have hsub : R' ⊆ R := Finset.filter_subset _ _
  have hbound : ∀ S : Finset E, ∃ C : ℝ, 0 ≤ C ∧ ∀ hS : S ∈ parabolics R' a,
      ∀ (Y : relativeSpace R a) (t : ℝ), 0 ≤ t →
      (∀ β : simpleRoots a (Q ∪ S), t ≤ ⟪((β : a) : E), (Y : E)⟫) →
      ∀ (u : relativeSpace R a → ℂ) (A : ℝ), 0 ≤ A →
        (∀ H, (1 + ‖H‖) ^ (n + Fintype.card (simpleRoots a S) + 1) * ‖phaseFourier u H‖ ≤ A) →
        ∀ D : Set (simpleRoots a S → ℝ), MeasurableSet D →
          (∀ X ∈ D, ∃ β : simpleRoots a (Q ∪ S), ∀ i : simpleRoots a S,
            (⟨i, simpleRoots_face_subset hR w hS i.property⟩ : simpleRoots a (Q ∪ S)) = β →
              X i ≤ 0) →
          ‖∫ X in D, phaseFourier u (Y - ∑ i, X i • chamberBasis hR ha
            (union_parabolic_of_local hR w hS).1 ⟨i, simpleRoots_face_subset hR w hS i.property⟩)‖ ≤
            C * A * ((1 + t) ^ n)⁻¹ := by
    intro S
    by_cases hS : S ∈ parabolics R' a
    · obtain ⟨C, hC, h⟩ := exists_orthant_term_bound hR ha (union_parabolic_of_local hR w hS).1
        (fun i : simpleRoots a S => (⟨i, simpleRoots_face_subset hR w hS i.property⟩ :
          simpleRoots a (Q ∪ S)))
        (fun i i' h => Subtype.ext (congrArg Subtype.val h :)) n
      exact ⟨C, hC, fun _ => h⟩
    · exact ⟨0, le_rfl, fun h => (hS h).elim⟩
  choose Cf hCf hb using hbound
  let gv (S : Finset E) : ℝ := gramVolume (fun v : simpleRoots a S => ((v : a) : E))
  have hgv (S : Finset E) : 0 ≤ gv S := Real.sqrt_nonneg _
  refine ⟨∑ S ∈ parabolics R' a, gv S * Cf S,
    Finset.sum_nonneg fun S _ => mul_nonneg (hgv S) (hCf S), fun Y t ht hY hYt u A hu => ?_⟩
  have hA : 0 ≤ A := le_trans (by positivity) (hu 0)
  have hyFam := isFamily_face hR w (isFamily_exp_of_orthogonal hY)
  have hu' : ∀ H, (1 + ‖H‖) ^ (Module.finrank ℝ (relativeSpace R a) + 1) *
      ‖phaseFourier (u : relativeSpace R a → ℂ) H‖ ≤ A := fun H =>
    le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀
      (le_add_of_nonneg_right (norm_nonneg H)) (by omega)) (norm_nonneg _)) (hu H)
  have hformula := integral_cM_exp_eq_orthants hR ha hR' ha' hsub
    (fun S hS => ⟨Q ∪ S, (union_parabolic_of_local hR w hS).1, simpleRoots_face_subset hR w hS⟩)
    (fun S => Y (Q ∪ S)) hyFam ξ hξ u hu'
  change ‖∫ x : relativeSpace R a, cM R' a (fun S Λ => exp (I * (Λ (Y (Q ∪ S)) : ℂ)))
    (dualParam R a x) * u x‖ ≤ _
  rw [hformula]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun S hS => ?_
  have hP := (union_parabolic_of_local hR w hS).1
  rw [norm_mul, norm_mul, orthantSign_abs, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (hgv S), mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hgv S)
  have hpt : ∀ X : simpleRoots a S → ℝ,
      (relativeSpace R a).orthogonalProjectionOnto
        ((Y (Q ∪ S) : E) - ∑ v : simpleRoots a S, X v • ((v : a) : E)) =
      (relativeSpace R a).orthogonalProjectionOnto (Y (Q ∪ S) : E) -
        ∑ v : simpleRoots a S, X v • chamberBasis hR ha hP
          ⟨v, simpleRoots_face_subset hR w hS v.property⟩ := fun X =>
    orthant_point_eq hR ha hP (simpleRoots_face_subset hR w hS) _ X
  simp_rw [hpt]
  have hcard : Fintype.card (simpleRoots a S) ≤ Module.finrank ℝ (relativeSpace R a) := by
    rw [Module.finrank_eq_card_basis (chamberBasis hR ha hP)]
    exact Fintype.card_le_of_injective
      (fun i : simpleRoots a S => (⟨i, simpleRoots_face_subset hR w hS i.property⟩ :
        simpleRoots a (Q ∪ S))) (fun i i' h => Subtype.ext (congrArg Subtype.val h :))
  obtain ⟨β₀, hβ₀P, hβ₀S⟩ := exists_simpleRoot_not_mem_face hR w hS hQ
  have h := hb S hS ((relativeSpace R a).orthogonalProjectionOnto (Y (Q ∪ S) : E)) t ht
    (fun β => by
      rw [inner_simpleRoot_projection hR ha hP β]
      exact hYt _ hP _ β.property)
    u A hA (fun H => le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀
      (le_add_of_nonneg_right (norm_nonneg H)) (by omega)) (norm_nonneg _)) (hu H))
    (orientedOrthant (fun v : simpleRoots a S => -dualParam R a ξ (v : a)))
    (Langlands.Analysis.measurableSet_orientedOrthant _)
    (fun (X : simpleRoots a S → ℝ) _ => ⟨⟨β₀, hβ₀P⟩, fun i hi => by
      exfalso
      have := congrArg Subtype.val hi
      simp only at this
      exact hβ₀S (this ▸ i.property)⟩)
  calc _ ≤ Cf S * A * ((1 + t) ^ n)⁻¹ := h
    _ = _ := by ring

/-- **The main term converges to `u(0)`.** For `ξ ∈ 𝔞_M^G` with `Λ_ξ` off the walls and `n ∈ ℕ` there
is `C ≥ 0` such that for every `t ≥ 0`, every positive `(G, M)`-orthogonal set `Y` with
`⟪v, Y_S⟫ ≥ t` for all chambers `S` and simple roots `v`, and every Schwartz `u` with
`(1 + ‖H‖)^{n + k + 1} |phaseFourier u H| ≤ A`, `k = dim 𝔞_M^G`,
`|(2π)^{−k} ∫ c_M(Λ_x) u(x) dx − u(0)| ≤ C A (1 + t)^{−n}`, `c_M` for the exponential family
`e^{λ(Y_S)}`. -/
theorem exists_main_term_bound (hR : IsRootSet R) (ha : IsLeviSpace R a)
    (ξ : relativeSpace R a) (hξ : OffWalls R a (dualParam R a ξ)) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y : Finset E → a) (t : ℝ), 0 ≤ t → IsPositiveOrthogonalSet R a Y →
      (∀ S ∈ parabolics R a, ∀ v ∈ simpleRoots a S, t ≤ ⟪v, Y S⟫) →
      ∀ (u : 𝓢(relativeSpace R a, ℂ)) (A : ℝ),
        (∀ H, (1 + ‖H‖) ^ (n + Module.finrank ℝ (relativeSpace R a) + 1) *
          ‖phaseFourier u H‖ ≤ A) →
        ‖((((2 * Real.pi) ^ Module.finrank ℝ (relativeSpace R a))⁻¹ : ℝ) : ℂ) *
            (∫ x : relativeSpace R a, cM R a (fun S Λ => exp (I * (Λ (Y S) : ℂ)))
              (dualParam R a x) * u x) - u 0‖ ≤ C * A * ((1 + t) ^ n)⁻¹ := by
  let Ps := parabolics R a
  let V := relativeSpace R a
  let k := Module.finrank ℝ V
  let pV := V.orthogonalProjectionOnto
  let d (S : Finset E) : simpleRoots a S → ℝ := fun v => -dualParam R a ξ (v : a)
  have hξα : ∀ α ∈ R, restrictedRoot a α ≠ 0 → ⟪(ξ : E), α⟫ ≠ 0 :=
    (offWalls_dualParam_iff ξ).mp hξ
  let w₀ : a := ⟨-(ξ : E), a.neg_mem ξ.property.1⟩
  have hreg : IsRegular R a (w₀ : E) := ⟨w₀.property, fun α hα hne => by
    change ⟪α, -(ξ : E)⟫ ≠ 0
    rw [inner_neg_right, neg_ne_zero, real_inner_comm]
    exact hξα α hα hne⟩
  let P₀ := posSet R (w₀ : E)
  have hP₀ : P₀ ∈ Ps := mem_parabolics_iff.mpr ⟨_, hreg, rfl⟩
  have hdval (S : Finset E) (v : simpleRoots a S) : d S v = ⟪((v : a) : E), (w₀ : E)⟫ := by
    simp only [d, dualParam_apply, w₀, inner_neg_right, real_inner_comm]
  have hd₀ : ∀ v : simpleRoots a P₀, 0 < d P₀ v := fun v => by
    rw [hdval]
    exact simpleRoot_pos (R := R) (h := w₀) v.property
  have hdne (P : Finset E) (hP : P ∈ Ps) (v : simpleRoots a P) : d P v ≠ 0 := by
    simp only [d, neg_ne_zero]
    exact apply_simpleRoot_ne_zero_of_offWalls hR ha subset_rfl hP hξ v.property
  have hother : ∀ P ∈ Ps, P ≠ P₀ → ∃ β : simpleRoots a P, d P β < 0 := by
    intro P hP hne
    by_contra hall
    push Not at hall
    have hpos : ∀ i : simpleRoots a P, 0 ≤ ⟪(i : a), w₀⟫ := fun i => by
      have := hall i
      rw [hdval] at this
      exact this
    have hsub : posSet R (w₀ : E) ⊆ P :=
      (posSet_subset_iff_nonneg hR hP w₀).mpr (nonneg_posSet_of_nonneg_simpleRoots hP w₀ hpos)
    exact hne (parabolic_eq_of_subset hR hP₀ (parabolics_subset_faces R a hP) hsub).symm
  have hbound : ∀ P : Finset E, ∃ C : ℝ, 0 ≤ C ∧ ∀ hP : P ∈ Ps,
      ∀ (Y : V) (t : ℝ), 0 ≤ t →
      (∀ β : simpleRoots a P, t ≤ ⟪((β : a) : E), (Y : E)⟫) →
      ∀ (u : V → ℂ) (A : ℝ), 0 ≤ A →
        (∀ H, (1 + ‖H‖) ^ (n + Fintype.card (simpleRoots a P) + 1) * ‖phaseFourier u H‖ ≤ A) →
        ∀ D : Set (simpleRoots a P → ℝ), MeasurableSet D →
          (∀ X ∈ D, ∃ β : simpleRoots a P, ∀ i : simpleRoots a P,
            (⟨i, (subset_rfl : simpleRoots a P ⊆ simpleRoots a P) i.property⟩ :
              simpleRoots a P) = β → X i ≤ 0) →
          ‖∫ X in D, phaseFourier u (Y - ∑ i, X i • chamberBasis hR ha hP
            ⟨i, (subset_rfl : simpleRoots a P ⊆ simpleRoots a P) i.property⟩)‖ ≤
            C * A * ((1 + t) ^ n)⁻¹ := by
    intro P
    by_cases hP : P ∈ Ps
    · obtain ⟨C, hC, h⟩ := exists_orthant_term_bound hR ha hP
        (fun i : simpleRoots a P => (⟨i, (subset_rfl : simpleRoots a P ⊆ simpleRoots a P)
          i.property⟩ : simpleRoots a P))
        (fun i i' h => Subtype.ext (congrArg Subtype.val h :)) n
      exact ⟨C, hC, fun _ => h⟩
    · exact ⟨0, le_rfl, fun h => (hP h).elim⟩
  choose Cf hCf hb using hbound
  let gv (S : Finset E) : ℝ := gramVolume (fun v : simpleRoots a S => ((v : a) : E))
  have hgv (S : Finset E) : 0 ≤ gv S := Real.sqrt_nonneg _
  refine ⟨∑ P ∈ Ps, gv P * Cf P, Finset.sum_nonneg fun P _ => mul_nonneg (hgv P) (hCf P),
    fun Y t ht hY hYt u A hu => ?_⟩
  have hA : 0 ≤ A := le_trans (by positivity) (hu 0)
  have hcardP (P : Finset E) (hP : P ∈ Ps) : Fintype.card (simpleRoots a P) = k :=
    (Module.finrank_eq_card_basis (chamberBasis hR ha hP)).symm
  have hu₁ : ∀ H, (1 + ‖H‖) ^ (k + 1) * ‖phaseFourier (u : V → ℂ) H‖ ≤ A := fun H =>
    le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀
      (le_add_of_nonneg_right (norm_nonneg H)) (Nat.succ_le_succ (Nat.le_add_left k n)))
      (norm_nonneg _)) (hu H)
  have hformula := integral_cM_exp_eq_orthants hR ha hR ha subset_rfl
    (fun S hS => ⟨S, hS, subset_rfl⟩) Y (isFamily_exp_of_orthogonal hY) ξ hξ u hu₁
  -- the integrand in coordinates
  let F (P : Finset E) (X : simpleRoots a P → ℝ) : ℂ :=
    phaseFourier u (pV ((Y P : E) - ∑ v : simpleRoots a P, X v • ((v : a) : E)))
  have hF (P : Finset E) (hP : P ∈ Ps) (X : simpleRoots a P → ℝ) :
      F P X = phaseFourier u (pV (Y P : E) - ∑ i, X i • chamberBasis hR ha hP
        ⟨i, (subset_rfl : simpleRoots a P ⊆ simpleRoots a P) i.property⟩) := by
    simp only [F]
    rw [orthant_point_eq hR ha hP (subset_rfl : simpleRoots a P ⊆ simpleRoots a P)]
  have hYP (P : Finset E) (hP : P ∈ Ps) : ∀ β : simpleRoots a P,
      t ≤ ⟪((β : a) : E), ((pV (Y P : E) : V) : E)⟫ := fun β => by
    rw [inner_simpleRoot_projection hR ha hP β]
    exact hYt _ hP _ β.property
  have huP (P : Finset E) (hP : P ∈ Ps) : ∀ H, (1 + ‖H‖) ^ (n + Fintype.card (simpleRoots a P) + 1) *
      ‖phaseFourier (u : V → ℂ) H‖ ≤ A := fun H => by
    rw [hcardP P hP]; exact hu H
  -- integrability and value for the chamber of `-ξ`
  have hint₀ : Integrable (F P₀) := by
    have h := integrable_orthant_phaseFourier hR ha hP₀
      (fun i : simpleRoots a P₀ => (⟨i, (subset_rfl : simpleRoots a P₀ ⊆ simpleRoots a P₀)
        i.property⟩ : simpleRoots a P₀))
      (fun i i' h => Subtype.ext (congrArg Subtype.val h :)) (pV (Y P₀ : E)) u
      (fun H => le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀
        (le_add_of_nonneg_right (norm_nonneg H)) (by rw [hcardP P₀ hP₀])) (norm_nonneg _)) (hu₁ H))
    refine h.congr (ae_of_all _ fun X => ?_)
    exact (hF P₀ hP₀ X).symm
  have hval₀ : (gv P₀ : ℂ) * ∫ X, F P₀ X = (2 * Real.pi : ℂ) ^ k * u 0 := by
    let b := chamberBasis hR ha hP₀
    have hcov := integral_eq_gramVolume_mul b (fun H => phaseFourier (u : V → ℂ) (pV (Y P₀ : E) - H))
    rw [integral_sub_left_eq_self (fun H => phaseFourier (u : V → ℂ) H), integral_phaseFourier] at hcov
    have hgvb : gramVolume (fun i => b i) = gv P₀ := by
      rw [← gramVolume_subtype V (fun i => b i)]
      exact congrArg gramVolume (funext fun i => chamberBasis_apply hR ha hP₀ i)
    rw [hgvb] at hcov
    rw [hcov]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun X => by rw [hF P₀ hP₀ X])
  have hsign₀ : orthantSign (d P₀) = 1 := by
    rw [orthantSign]
    exact Finset.prod_eq_one fun v _ => by simp only [hd₀ v, ite_true]
  -- the decomposition
  set κ : ℝ := ((2 * Real.pi) ^ k)⁻¹ with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hκ1 : κ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [Real.two_le_pi]))
  have hκmul : (κ : ℂ) * (2 * Real.pi : ℂ) ^ k = 1 := by
    rw [hκ]; push_cast
    exact inv_mul_cancel₀ (pow_ne_zero _ (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  let f (P : Finset E) : ℂ := (gv P : ℂ) * (orthantSign (d P) * ∫ X in orientedOrthant (d P), F P X)
  have hT : ∫ x : V, cM R a (fun S Λ => exp (I * (Λ (Y S) : ℂ))) (dualParam R a x) * u x =
      ∑ P ∈ Ps, f P := hformula
  have hcompl : ∫ X in orientedOrthant (d P₀), F P₀ X =
      (∫ X, F P₀ X) - ∫ X in (orientedOrthant (d P₀))ᶜ, F P₀ X := by
    rw [← integral_add_compl (Langlands.Analysis.measurableSet_orientedOrthant (d P₀)) hint₀]; ring
  have hf₀ : f P₀ = (2 * Real.pi : ℂ) ^ k * u 0 -
      (gv P₀ : ℂ) * ∫ X in (orientedOrthant (d P₀))ᶜ, F P₀ X := by
    simp only [f]
    rw [hsign₀, one_mul, hcompl, mul_sub, hval₀]
  have hmain : ((κ : ℝ) : ℂ) * (∑ P ∈ Ps, f P) - u 0 = (κ : ℂ) *
      (-( (gv P₀ : ℂ) * ∫ X in (orientedOrthant (d P₀))ᶜ, F P₀ X) +
        ∑ P ∈ Ps.erase P₀, f P) := by
    rw [← Finset.add_sum_erase Ps f hP₀, hf₀]
    linear_combination (u 0) * hκmul
  rw [hT, hmain, norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ0]
  -- bounds for the pieces
  have hbound₀ : ‖∫ X in (orientedOrthant (d P₀))ᶜ, F P₀ X‖ ≤ Cf P₀ * A * ((1 + t) ^ n)⁻¹ := by
    have h := hb P₀ hP₀ (pV (Y P₀ : E)) t ht (hYP P₀ hP₀) u A hA (huP P₀ hP₀)
      (orientedOrthant (d P₀))ᶜ (Langlands.Analysis.measurableSet_orientedOrthant _).compl (fun X hX => by
        rw [orientedOrthant_eq, Set.mem_compl_iff, Set.mem_univ_pi] at hX
        push Not at hX
        obtain ⟨β, hβ⟩ := hX
        refine ⟨β, fun i hi => ?_⟩
        have hiβ : i = β := Subtype.ext (congrArg Subtype.val hi :)
        rw [hiβ]
        simp only [hd₀ β, ite_true, Set.mem_Ioi, not_lt] at hβ
        exact hβ)
    refine le_of_eq_of_le ?_ h
    congr 1
    exact setIntegral_congr_fun (Langlands.Analysis.measurableSet_orientedOrthant _).compl fun X _ => hF P₀ hP₀ X
  have hboundP : ∀ P ∈ Ps.erase P₀, ‖f P‖ ≤ gv P * (Cf P * A * ((1 + t) ^ n)⁻¹) := by
    intro P hP
    obtain ⟨hne, hP⟩ := Finset.mem_erase.mp hP
    obtain ⟨β, hβ⟩ := hother P hP hne
    have h := hb P hP (pV (Y P : E)) t ht (hYP P hP) u A hA (huP P hP)
      (orientedOrthant (d P)) (Langlands.Analysis.measurableSet_orientedOrthant _) (fun X hX => by
        rw [orientedOrthant_eq] at hX
        refine ⟨β, fun i hi => ?_⟩
        have hiβ : i = β := Subtype.ext (congrArg Subtype.val hi :)
        rw [hiβ]
        have := hX β (Set.mem_univ _)
        simp only [not_lt.mpr hβ.le, ite_false, Set.mem_Iio] at this
        exact this.le)
    simp only [f]
    rw [norm_mul, norm_mul, orthantSign_abs, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (hgv P)]
    refine mul_le_mul_of_nonneg_left (le_of_eq_of_le ?_ h) (hgv P)
    congr 1
    exact setIntegral_congr_fun (Langlands.Analysis.measurableSet_orientedOrthant _) fun X _ => hF P hP X
  have hsumP : ‖∑ P ∈ Ps.erase P₀, f P‖ ≤ ∑ P ∈ Ps.erase P₀, gv P * (Cf P * A * ((1 + t) ^ n)⁻¹) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum hboundP)
  have hpos : 0 ≤ A * ((1 + t) ^ n)⁻¹ := by positivity
  calc κ * ‖-((gv P₀ : ℂ) * ∫ X in (orientedOrthant (d P₀))ᶜ, F P₀ X) + ∑ P ∈ Ps.erase P₀, f P‖
      ≤ 1 * (gv P₀ * (Cf P₀ * A * ((1 + t) ^ n)⁻¹) +
          ∑ P ∈ Ps.erase P₀, gv P * (Cf P * A * ((1 + t) ^ n)⁻¹)) := by
        refine mul_le_mul hκ1 ((norm_add_le _ _).trans (add_le_add ?_ hsumP)) (norm_nonneg _)
          zero_le_one
        rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hgv P₀)]
        exact mul_le_mul_of_nonneg_left hbound₀ (hgv P₀)
    _ = (∑ P ∈ Ps, gv P * Cf P) * A * ((1 + t) ^ n)⁻¹ := by
        rw [one_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.add_sum_erase Ps
            (fun P => gv P * Cf P * A * ((1 + t) ^ n)⁻¹) hP₀]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun P _ => by ring

end Langlands.GMFamily
