import Langlands.LinearAlgebra.GMFamiliesStatement
import Langlands.LinearAlgebra.GMFamilyWallWeights

/-! # Smooth extension of the weighted sum of a `(G, M)`-family -/

noncomputable section

open Classical
open scoped RealInnerProductSpace ContDiff

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {a : Submodule ℝ E} {R : Finset E}

private abbrev normalLine (v : a) : Submodule ℝ a := ℝ ∙ v

omit [FiniteDimensional ℝ E] in
private theorem normalLine_neg (v : a) : normalLine (-v) = normalLine v := by
  simpa only [neg_one_smul] using Submodule.span_singleton_smul_eq (isUnit_neg_one (α := ℝ)) v

private def chamberLines (a : Submodule ℝ E) (S : Finset E) : Finset (Submodule ℝ a) :=
  (simpleRoots a S).image normalLine

private def wallLines (R : Finset E) (a : Submodule ℝ E) : Finset (Submodule ℝ a) :=
  (parabolics R a).biUnion (chamberLines a)

private theorem chamberLines_subset {S : Finset E} (hS : S ∈ parabolics R a) :
    chamberLines a S ⊆ wallLines R a :=
  fun _ h => Finset.mem_biUnion.mpr ⟨S, hS, h⟩

private def normalVector (L : Submodule ℝ a) : a :=
  if h : ∃ v : a, v ≠ 0 ∧ normalLine v = L then h.choose else 0

omit [FiniteDimensional ℝ E] in
private theorem normalVector_spec {L : Submodule ℝ a}
    (h : ∃ v : a, v ≠ 0 ∧ normalLine v = L) :
    normalVector L ≠ 0 ∧ normalLine (normalVector L) = L := by
  rw [normalVector, dite_eq_left h]
  exact h.choose_spec

private theorem simpleRoot_ne_zero {S : Finset E} (hS : S ∈ parabolics R a) {v : a}
    (hv : v ∈ simpleRoots a S) : v ≠ 0 := by
  obtain ⟨_, ⟨x, hx, rfl⟩⟩ := Finset.mem_filter.mp hS
  have hp := simpleRoot_pos (h := (⟨x, hx.1⟩ : a)) hv
  intro hz
  rw [hz, inner_zero_left] at hp
  exact (lt_irrefl _) hp

private theorem normalVector_of_mem {L : Submodule ℝ a} (hL : L ∈ wallLines R a) :
    normalVector L ≠ 0 ∧ normalLine (normalVector L) = L := by
  obtain ⟨S, hS, hsL⟩ := Finset.mem_biUnion.mp hL
  obtain ⟨v, hv, hvL⟩ := Finset.mem_image.mp hsL
  exact normalVector_spec ⟨v, simpleRoot_ne_zero hS hv, hvL⟩

private def normalMultiplier (v : a) : ℝ :=
  ⟪v, normalVector (normalLine v)⟫ / ⟪normalVector (normalLine v), normalVector (normalLine v)⟫

omit [FiniteDimensional ℝ E] in
private theorem normalMultiplier_neg (v : a) : normalMultiplier (-v) = -normalMultiplier v := by
  rw [normalMultiplier, normalLine_neg, inner_neg_left, neg_div, normalMultiplier]

omit [FiniteDimensional ℝ E] in
private theorem normalMultiplier_spec {v : a} (hv : v ≠ 0) :
    v = normalMultiplier v • normalVector (normalLine v) ∧ normalMultiplier v ≠ 0 := by
  let n := normalVector (normalLine v)
  obtain ⟨hn0, hn⟩ := normalVector_spec ⟨v, hv, rfl⟩
  have hmem : v ∈ normalLine n := hn.symm ▸ Submodule.mem_span_singleton_self v
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
  have he : normalMultiplier v = r := by
    change ⟪v, n⟫ / ⟪n, n⟫ = r
    rw [← hr, real_inner_smul_left]
    exact mul_div_cancel_right₀ r (real_inner_self_pos.mpr hn0).ne'
  refine ⟨he.symm ▸ hr.symm, fun hz => hv ?_⟩
  rw [← hr, ← he, hz, zero_smul]

private def wallEvaluation (L : Submodule ℝ a) : StrongDual ℝ a →L[ℝ] ℝ :=
  ContinuousLinearMap.apply ℝ ℝ (normalVector L)

private theorem wallEvaluation_nonzero {L : Submodule ℝ a} (hL : L ∈ wallLines R a) :
    wallEvaluation L ≠ 0 := by
  have hv := (normalVector_of_mem hL).1
  intro h
  exact (real_inner_self_pos.mpr hv).ne' (DFunLike.congr_fun h (innerSL ℝ (normalVector L)))

private theorem wallEvaluation_separate {L K : Submodule ℝ a} (hL : L ∈ wallLines R a)
    (hK : K ∈ wallLines R a) (hn : L ≠ K) :
    ∃ Λ : StrongDual ℝ a, wallEvaluation L Λ = 0 ∧ wallEvaluation K Λ ≠ 0 := by
  have hL' := (normalVector_of_mem hL).2
  obtain ⟨hK₀, hK'⟩ := normalVector_of_mem hK
  have hmem : normalVector K ∉ L := by
    intro h
    have hw : normalVector K ∈ normalLine (normalVector L) := hL'.symm ▸ h
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hw
    have hr0 : r ≠ 0 := fun he => hK₀ (by rw [← hr, he, zero_smul])
    apply hn
    rw [← hL', ← hK', ← hr]
    exact (Submodule.span_singleton_smul_eq hr0.isUnit _).symm
  obtain ⟨f, hfK, hfL⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (R := ℝ) hmem inferInstance
  refine ⟨f.toContinuousLinearMap, ?_, hfK⟩
  have hm : normalVector L ∈ normalLine (normalVector L) := Submodule.mem_span_singleton_self _
  rw [hL'] at hm
  have hh : f (normalVector L) ∈ L.map f := Submodule.mem_map_of_mem hm
  rw [hfL] at hh
  exact (Submodule.mem_bot ℝ).mp hh

omit [FiniteDimensional ℝ E] in
private theorem parameterFactor_multiplier {v : a} (hv : v ≠ 0) (Λ : StrongDual ℝ a) :
    parameterFactor v Λ = (normalMultiplier v : ℂ) * imaginaryFactor (wallEvaluation (normalLine v)) Λ := by
  have he := congrArg Λ (normalMultiplier_spec hv).1
  change Λ v = Λ (normalMultiplier v • normalVector (normalLine v)) at he
  rw [map_smul, smul_eq_mul] at he
  unfold parameterFactor imaginaryFactor
  change Complex.I * (Λ v : ℂ) = (normalMultiplier v : ℂ) * (Complex.I * (Λ (normalVector (normalLine v)) : ℂ))
  rw [he, Complex.ofReal_mul]
  ring

omit [FiniteDimensional ℝ E] in
private theorem parameterProduct_eq (s : Finset a) (hn : ∀ v ∈ s, v ≠ 0)
    (hi : Set.InjOn normalLine (s : Set a)) (Λ : StrongDual ℝ a) :
    (∏ v ∈ s, parameterFactor v Λ) = (∏ v ∈ s, (normalMultiplier v : ℂ)) *
      ∏ L ∈ s.image normalLine, imaginaryFactor (wallEvaluation L) Λ := by
  rw [Finset.prod_image (fun x hx y hy h => hi hx hy h), ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v hv => parameterFactor_multiplier (hn v hv) Λ

private theorem chamberLines_erase {S : Finset E} {v : a}
    (hinj : Set.InjOn normalLine (simpleRoots a S : Set a)) (hv : v ∈ simpleRoots a S) :
    ((simpleRoots a S).erase v).image normalLine = (chamberLines a S).erase (normalLine v) := by
  ext L
  simp only [chamberLines, Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨u, ⟨hne, hu⟩, rfl⟩
    exact ⟨fun he => hne (hinj hu hv he), u, hu, rfl⟩
  · rintro ⟨hne, u, hu, rfl⟩
    exact ⟨u, ⟨fun he => hne (congrArg normalLine he), hu⟩, rfl⟩

private def chamberVolume (a : Submodule ℝ E) (S : Finset E) : ℂ :=
  (gramVolume (fun i : simpleRoots a S => ((i : a) : E)) : ℝ)

private def multiplierProduct (a : Submodule ℝ E) (S : Finset E) : ℂ :=
  ∏ v ∈ simpleRoots a S, (normalMultiplier v : ℂ)

private theorem multiplierProduct_ne_zero {S : Finset E} (hS : S ∈ parabolics R a) :
    multiplierProduct a S ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hv => Complex.ofReal_ne_zero.mpr
    (normalMultiplier_spec (simpleRoot_ne_zero hS hv)).2

private abbrev wallProduct (s : Finset (Submodule ℝ a)) : StrongDual ℝ a → ℂ :=
  imaginaryProduct s wallEvaluation

private def clearedTerm (c : Finset E → StrongDual ℝ a → ℂ) (S : Finset E) (Λ : StrongDual ℝ a) : ℂ :=
  c S Λ * chamberVolume a S * (multiplierProduct a S)⁻¹ *
    wallProduct (wallLines R a \ chamberLines a S) Λ

set_option maxHeartbeats 3000000 in
omit [FiniteDimensional ℝ E] in
private theorem contDiff_wallProduct (s : Finset (Submodule ℝ a)) :
    ContDiff ℝ ∞ (wallProduct s) := by
  have h := contDiff_imaginaryProduct (V := StrongDual ℝ a) s (fun L => wallEvaluation L)
  exact h

private theorem contDiff_clearedTerm {c : Finset E → StrongDual ℝ a → ℂ} {S : Finset E}
    (hc : IsFamily R a c) (hS : S ∈ parabolics R a) : ContDiff ℝ ∞ (clearedTerm (R := R) c S) := by
  unfold clearedTerm
  exact (((hc.1 S hS).mul (contDiff_const (c := chamberVolume a S))).mul
    (contDiff_const (c := (multiplierProduct a S)⁻¹))).mul
      (contDiff_wallProduct (wallLines R a \ chamberLines a S))

private theorem clearedTerm_mul_on_wall {S : Finset E} {v : a} (hR : IsRootSet R) (ha : IsLeviSpace R a)
    (hS : S ∈ parabolics R a) (hv : v ∈ simpleRoots a S) (c : Finset E → StrongDual ℝ a → ℂ)
    (Λ : StrongDual ℝ a) :
    clearedTerm (R := R) c S Λ * ((normalMultiplier v : ℂ) *
      ∏ u ∈ (simpleRoots a S).erase v, parameterFactor u Λ) =
      c S Λ * chamberVolume a S * wallProduct ((wallLines R a).erase (normalLine v)) Λ := by
  let L := normalLine v
  have hinj := simpleRoots_injOn_line hR ha hS
  have hep := parameterProduct_eq ((simpleRoots a S).erase v)
    (fun u hu => simpleRoot_ne_zero hS (Finset.mem_of_mem_erase hu))
    (fun _ hu _ hw he => hinj (Finset.mem_of_mem_erase hu) (Finset.mem_of_mem_erase hw) he) Λ
  rw [chamberLines_erase hinj hv] at hep
  have hm : (normalMultiplier v : ℂ) * (∏ u ∈ (simpleRoots a S).erase v, (normalMultiplier u : ℂ)) =
      multiplierProduct a S :=
    Finset.mul_prod_erase (simpleRoots a S) (fun u => (normalMultiplier u : ℂ)) hv
  have hL : L ∈ chamberLines a S := Finset.mem_image_of_mem _ hv
  have hsub : (chamberLines a S).erase L ⊆ (wallLines R a).erase L := by
    intro K hK
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hK).1, chamberLines_subset hS (Finset.mem_of_mem_erase hK)⟩
  have hd : (wallLines R a).erase L \ (chamberLines a S).erase L = wallLines R a \ chamberLines a S := by
    ext K
    by_cases h : K = L
    · subst K; simp [hL]
    · simp [h]
  have hp : wallProduct (wallLines R a \ chamberLines a S) Λ *
      wallProduct ((chamberLines a S).erase L) Λ = wallProduct ((wallLines R a).erase L) Λ := by
    unfold wallProduct imaginaryProduct
    rw [← hd, Finset.prod_sdiff hsub]
  rw [hep]
  change _ * ((normalMultiplier v : ℂ) * ((∏ u ∈ (simpleRoots a S).erase v,
    (normalMultiplier u : ℂ)) * wallProduct ((chamberLines a S).erase L) Λ)) = _
  rw [← mul_assoc (normalMultiplier v : ℂ), hm, clearedTerm, ← hp]
  have hn := multiplierProduct_ne_zero hS
  field_simp [hn]

private theorem clearedTerm_mul_theta {S : Finset E} (hR : IsRootSet R) (ha : IsLeviSpace R a)
    (hS : S ∈ parabolics R a) (c : Finset E → StrongDual ℝ a → ℂ) (Λ : StrongDual ℝ a)
    (hθ : theta a S Λ ≠ 0) :
    clearedTerm (R := R) c S Λ * theta a S Λ = c S Λ * wallProduct (wallLines R a) Λ := by
  have he := parameterProduct_eq (simpleRoots a S) (fun v hv => simpleRoot_ne_zero hS hv)
    (simpleRoots_injOn_line hR ha hS) Λ
  have hvol : chamberVolume a S ≠ 0 := by
    intro hz
    apply hθ
    rw [theta_eq_product]
    change (chamberVolume a S)⁻¹ * (∏ u ∈ simpleRoots a S, parameterFactor u Λ) = 0
    rw [hz, inv_zero, zero_mul]
  have hp : wallProduct (wallLines R a \ chamberLines a S) Λ * wallProduct (chamberLines a S) Λ =
      wallProduct (wallLines R a) Λ := Finset.prod_sdiff (chamberLines_subset hS)
  rw [theta_eq_product, he]
  change clearedTerm (R := R) c S Λ * ((chamberVolume a S)⁻¹ * (multiplierProduct a S *
    wallProduct (chamberLines a S) Λ)) = _
  rw [clearedTerm, ← hp]
  field_simp [hvol, multiplierProduct_ne_zero hS]

private theorem clearedTerm_add_adjacent {S T : Finset E} {v : a}
    (hR : IsRootSet R) (ha : IsLeviSpace R a) (hS : S ∈ parabolics R a) (hT : T ∈ parabolics R a)
    (hA : IsAdjacentAlong R a S T v) {c : Finset E → StrongDual ℝ a → ℂ} (hc : IsFamily R a c)
    (Λ : StrongDual ℝ a) (hz : wallEvaluation (normalLine v) Λ = 0)
    (hn : ∀ L ∈ (wallLines R a).erase (normalLine v), wallEvaluation L Λ ≠ 0) :
    clearedTerm (R := R) c S Λ + clearedTerm (R := R) c T Λ = 0 := by
  have hv := simpleRoot_ne_zero hS hA.1
  have hzero : imaginaryFactor (wallEvaluation (normalLine v)) Λ = 0 := imaginaryFactor_eq_zero.mpr hz
  have hΛ : Λ v = 0 := (parameterFactor_eq_zero Λ v).mp (by
    rw [parameterFactor_multiplier hv, hzero, mul_zero])
  obtain ⟨hvol, hep⟩ := volume_and_product_erase_of_adjacentAlong hR ha hS hT hA
  have hV : chamberVolume a S = chamberVolume a T := congrArg Complex.ofReal hvol
  have hval := hc.2 S hS T hT v hA Λ hΛ
  have hS' := clearedTerm_mul_on_wall hR ha hS hA.1 c Λ
  have hT' := clearedTerm_mul_on_wall hR ha hT hA.2.1 c Λ
  rw [normalMultiplier_neg, Complex.ofReal_neg, ← hep Λ hΛ, normalLine_neg, ← hval, ← hV] at hT'
  let Q := (normalMultiplier v : ℂ) * ∏ u ∈ (simpleRoots a S).erase v, parameterFactor u Λ
  have hQ : Q ≠ 0 := by
    refine mul_ne_zero (Complex.ofReal_ne_zero.mpr (normalMultiplier_spec hv).2) ?_
    apply Finset.prod_ne_zero_iff.mpr
    intro u hu
    obtain ⟨huv, huS⟩ := Finset.mem_erase.mp hu
    have huL : normalLine u ∈ (wallLines R a).erase (normalLine v) := by
      apply Finset.mem_erase.mpr
      exact ⟨fun h => huv ((simpleRoots_injOn_line hR ha hS) huS hA.1 h),
        chamberLines_subset hS (Finset.mem_image_of_mem _ huS)⟩
    have hu₀ := simpleRoot_ne_zero hS huS
    rw [parameterFactor_multiplier hu₀]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (normalMultiplier_spec hu₀).2)
      (fun h => hn _ huL (imaginaryFactor_eq_zero.mp h))
  apply mul_right_cancel₀ hQ
  rw [add_mul, zero_mul]
  change clearedTerm (R := R) c S Λ * Q + clearedTerm (R := R) c T Λ * Q = 0
  change clearedTerm (R := R) c S Λ * Q = _ at hS'
  rw [neg_mul, mul_neg] at hT'
  change -(clearedTerm (R := R) c T Λ * Q) = _ at hT'
  rw [hS', ← hT', neg_add_cancel]

set_option maxHeartbeats 1000000 in
private theorem sum_clearedTerm_vanishes {c : Finset E → StrongDual ℝ a → ℂ}
    (hR : IsRootSet R) (ha : IsLeviSpace R a) (hc : IsFamily R a c)
    (L : Submodule ℝ a) (hL : L ∈ wallLines R a)
    (Λ : StrongDual ℝ a) (hz : wallEvaluation L Λ = 0)
    (hn : ∀ K ∈ (wallLines R a).erase L, wallEvaluation K Λ ≠ 0) :
    (∑ S ∈ parabolics R a, clearedTerm (R := R) c S Λ) = 0 := by
  let P := (parabolics R a).filter (fun S => L ∈ chamberLines a S)
  have hsplit := Finset.sum_filter_add_sum_filter_not (parabolics R a)
    (fun S => L ∈ chamberLines a S) (fun S => clearedTerm (R := R) c S Λ)
  rw [← hsplit]
  have hzero : ∑ S ∈ (parabolics R a).filter (fun S => L ∉ chamberLines a S),
      clearedTerm (R := R) c S Λ = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    have hnot := (Finset.mem_filter.mp hS).2
    have hfac : imaginaryFactor (wallEvaluation L) Λ = 0 := imaginaryFactor_eq_zero.mpr hz
    have hprod : wallProduct (wallLines R a \ chamberLines a S) Λ = 0 :=
      Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨hL, hnot⟩) hfac
    rw [clearedTerm, hprod, mul_zero]
  rw [hzero, add_zero]
  change (∑ S ∈ P, clearedTerm (R := R) c S Λ) = 0
  have hS (S : Finset E) (h : S ∈ P) : S ∈ parabolics R a := (Finset.mem_filter.mp h).1
  have hex (S : Finset E) (h : S ∈ P) : ∃ v ∈ simpleRoots a S, normalLine v = L :=
    Finset.mem_image.mp (Finset.mem_filter.mp h).2
  let root (S : Finset E) (h : S ∈ P) := (hex S h).choose
  have hroot (S : Finset E) (h : S ∈ P) : root S h ∈ simpleRoots a S := (hex S h).choose_spec.1
  have hline (S : Finset E) (h : S ∈ P) : normalLine (root S h) = L := (hex S h).choose_spec.2
  have hexPartner (S : Finset E) (h : S ∈ P) :
      ∃ T ∈ parabolics R a, IsAdjacentAlong R a S T (root S h) :=
    exists_adjacentAlong hR ha (hS S h) (hroot S h)
  let partner (S : Finset E) (h : S ∈ P) := (hexPartner S h).choose
  have hpartner (S : Finset E) (h : S ∈ P) : partner S h ∈ parabolics R a := (hexPartner S h).choose_spec.1
  have hadj (S : Finset E) (h : S ∈ P) : IsAdjacentAlong R a S (partner S h) (root S h) :=
    (hexPartner S h).choose_spec.2
  have hmem (S : Finset E) (h : S ∈ P) : partner S h ∈ P := by
    refine Finset.mem_filter.mpr ⟨hpartner S h, ?_⟩
    exact Finset.mem_image.mpr ⟨-root S h, (hadj S h).2.1, (normalLine_neg _).trans (hline S h)⟩
  refine Finset.sum_involution partner (fun S h => ?_) (fun S h _ => ?_) hmem (fun S h => ?_)
  · exact clearedTerm_add_adjacent hR ha (hS S h) (hpartner S h) (hadj S h) hc Λ
      (hline S h ▸ hz) (hline S h ▸ hn)
  · exact (adjacentAlong_ne (hS S h) (hadj S h)).symm
  · let T := partner S h
    have hT : T ∈ P := hmem S h
    have hrev : root T hT = -root S h :=
      (simpleRoots_injOn_line hR ha (hpartner S h)) (hroot T hT) (hadj S h).2.1
        ((hline T hT).trans ((normalLine_neg _).trans (hline S h)).symm)
    exact adjacentAlong_unique (hpartner T hT) (hS S h) (hadj T hT)
      (hrev.symm ▸ (hadj S h).symm)

set_option maxHeartbeats 1000000 in
/-- Arthur 2005, Lemma 17.1. The weighted sum of a `(G, M)`-family extends smoothly. -/
theorem smoothExtension : SmoothExtensionStatement := by
  intro E _ _ _ R a hR ha c hc
  let D := wallLines R a
  let N (Λ : StrongDual ℝ a) := ∑ S ∈ parabolics R a, clearedTerm (R := R) c S Λ
  have hN : ContDiff ℝ ∞ N := ContDiff.sum (fun S hS => contDiff_clearedTerm hc hS)
  have hsep : ∀ L ∈ D, ∀ K ∈ D, L ≠ K →
      ∃ Λ : StrongDual ℝ a, wallEvaluation L Λ = 0 ∧ wallEvaluation K Λ ≠ 0 :=
    fun _ hL _ hK hn => wallEvaluation_separate hL hK hn
  have hz (L : Submodule ℝ a) (hL : L ∈ D) : ∀ Λ, wallEvaluation L Λ = 0 → N Λ = 0 :=
    vanishes_on_wall_of_vanishes_off_others (D.erase L) wallEvaluation (wallEvaluation L)
      (fun K hK => hsep L hL K (Finset.mem_of_mem_erase hK) (Finset.mem_erase.mp hK).1.symm)
      hN.continuous (sum_clearedTerm_vanishes hR ha hc L hL)
  obtain ⟨f, hf, he⟩ := smooth_factor_hyperplanes D wallEvaluation
    (fun _ hL => wallEvaluation_nonzero hL) hsep hN hz
  refine ⟨f, hf, fun Λ hθ => ?_⟩
  have hD : wallProduct D Λ ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro L hL hzero
    obtain ⟨S, hS, hLS⟩ := Finset.mem_biUnion.mp hL
    obtain ⟨v, hv, hvL⟩ := Finset.mem_image.mp hLS
    have hv0 := simpleRoot_ne_zero hS hv
    have hfac : parameterFactor v Λ = 0 := by rw [parameterFactor_multiplier hv0, hvL, hzero, mul_zero]
    apply hθ S hS
    rw [theta_eq_product, Finset.prod_eq_zero hv hfac, mul_zero]
  have hnum : N Λ = wallProduct D Λ * cM R a c Λ := by
    unfold N cM
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    have h := clearedTerm_mul_theta hR ha hS c Λ (hθ S hS)
    calc
      clearedTerm (R := R) c S Λ = (clearedTerm (R := R) c S Λ * theta a S Λ) * (theta a S Λ)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ (hθ S hS), mul_one]
      _ = wallProduct D Λ * (c S Λ * (theta a S Λ)⁻¹) := by rw [h]; ring
  exact mul_left_cancel₀ hD ((he Λ).symm.trans hnum)

end Langlands.GMFamily
