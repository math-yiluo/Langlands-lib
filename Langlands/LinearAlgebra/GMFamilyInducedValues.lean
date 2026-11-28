import Langlands.LinearAlgebra.GMFamiliesRoots
import Langlands.LinearAlgebra.FiniteHyperplaneChamberGallery

/-! # Values of the induced family on Levi chambers -/

noncomputable section

open scoped RealInnerProductSpace
open Submodule Classical
open Langlands.LinearAlgebra.FiniteHyperplaneSegment

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {R : Finset E} {a a₁ : Submodule ℝ E}

/-- The roots that cut out genuine hyperplanes on the Levi space. -/
def activeRoots (R : Finset E) (a : Submodule ℝ E) : Finset E :=
  R.filter fun x => restrictedRoot a x ≠ 0

/-- The active root as a linear form on the Levi space. -/
def rootForm (i : activeRoots R a) : Module.Dual ℝ a := innerₗ a (restrictedRoot a (i : E))

theorem rootForm_apply (i : activeRoots R a) (p : a) :
    rootForm i p = ⟪(i : E), (p : E)⟫ := inner_restrictedRoot p.prop

theorem rootForm_ne_zero (i : activeRoots R a) : rootForm i ≠ 0 := by
  intro hz
  have hval := congrArg (fun f : Module.Dual ℝ a => f (restrictedRoot a (i : E))) hz
  change ⟪restrictedRoot a (i : E), restrictedRoot a (i : E)⟫ = 0 at hval
  exact (Finset.mem_filter.mp i.prop).2 (inner_self_eq_zero.mp hval)

theorem isRegular_iff_rootForm (p : a) : IsRegular R a p ↔ Regular (rootForm (R := R) (a := a)) p := by
  refine ⟨fun h i => ?_, fun h => ⟨p.prop, fun x hx hx0 => ?_⟩⟩
  · rw [rootForm_apply]
    exact h.2 _ (Finset.mem_filter.mp i.prop).1 (Finset.mem_filter.mp i.prop).2
  · exact fun he => h ⟨x, Finset.mem_filter.mpr ⟨hx, hx0⟩⟩ (by rwa [rootForm_apply])

theorem restrictedRoot_nested (haa₁ : a ≤ a₁) (x : E) :
    restrictedRoot a (restrictedRoot a₁ x : E) = restrictedRoot a x :=
  orthogonalProjectionOnto_starProjection_of_le haa₁ x

private theorem pairing_eq_zero_of_inactive {p : a} {x : E} (hx : restrictedRoot a x = 0) :
    ⟪x, (p : E)⟫ = 0 := by rw [← inner_restrictedRoot p.prop, hx]; simp

private theorem posSet_eq_of_sameChamber {p q : a}
    (hpq : SameChamber (rootForm (R := R) (a := a)) p q) : posSet R (p : E) = posSet R (q : E) := by
  ext x
  simp only [mem_posSet_iff]
  refine and_congr_right fun hx => ?_
  by_cases h : restrictedRoot a x = 0
  · rw [pairing_eq_zero_of_inactive (p := p) h, pairing_eq_zero_of_inactive (p := q) h]
  · let i : activeRoots R a := ⟨x, Finset.mem_filter.mpr ⟨hx, h⟩⟩
    rcases mul_pos_iff.mp (hpq i) with hp | hp
    · exact iff_of_true (by simpa only [rootForm_apply] using hp.1)
        (by simpa only [rootForm_apply] using hp.2)
    · exact iff_of_false (not_lt_of_gt (by simpa only [rootForm_apply] using hp.1))
        (not_lt_of_gt (by simpa only [rootForm_apply] using hp.2))

omit [FiniteDimensional ℝ E] in
private theorem mem_posSet_neg_iff (hR : IsRootSet R) {x p : E} :
    -x ∈ posSet R p ↔ x ∈ R ∧ ⟪x, p⟫ < 0 := by
  rw [mem_posSet_iff, neg_mem_rootSet_iff hR, inner_neg_left, neg_pos]

private theorem posSet_wall_adjacent (hR : IsRootSet R) (keep : activeRoots R a → Prop)
    {p q : a} (hpq : WallAdjacent (rootForm (R := R) (a := a)) keep p q) :
    ∃ i : activeRoots R a, ¬ keep i ∧ IsAdjacentAlong R a (posSet R (p : E))
      (posSet R (q : E)) (restrictedRoot a (i : E)) := by
  obtain ⟨_, _, w, ⟨j, hj⟩, hflip, hfixed, hprop, hkeep⟩ := hpq
  let f := rootForm (R := R) (a := a)
  let T : Finset (activeRoots R a) := Finset.univ.filter fun i => f i w = 0 ∧ 0 < f i p
  have hnonempty : T.Nonempty := by
    rcases mul_neg_iff.mp (hflip j hj) with h | h
    · exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, h.1⟩⟩
    · let j' : activeRoots R a := ⟨-(j : E), Finset.mem_filter.mpr
        ⟨neg_mem_rootSet hR (Finset.mem_filter.mp j.prop).1, by
          change a.orthogonalProjectionOnto (-(j : E)) ≠ 0
          rw [map_neg, neg_ne_zero]
          exact (Finset.mem_filter.mp j.prop).2⟩⟩
      refine ⟨j', Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
      · change rootForm j' w = 0
        rw [rootForm_apply, inner_neg_left, ← rootForm_apply j w, hj, neg_zero]
      · change 0 < rootForm j' p
        rw [rootForm_apply, inner_neg_left, ← rootForm_apply j p, neg_pos]
        exact h.1
  obtain ⟨i, hi, hmin⟩ := T.exists_min_image (fun i => f i p) hnonempty
  have hiw : f i w = 0 := (Finset.mem_filter.mp hi).2.1
  have hip : 0 < f i p := (Finset.mem_filter.mp hi).2.2
  have hiq : f i q < 0 := (mul_neg_iff.mp (hflip i hiw)).resolve_right
    (fun hh => (not_lt_of_gt hip) hh.1) |>.2
  let v : a := restrictedRoot a (i : E)
  have hroot (x : a) {r : E} (hr : r ∈ posSet R (x : E)) :
      ∃ j : activeRoots R a, (j : E) = r ∧ 0 < f j x := by
    obtain ⟨hrR, hrp⟩ := mem_posSet_iff.mp hr
    refine ⟨⟨r, Finset.mem_filter.mpr ⟨hrR, fun hz => ?_⟩⟩, rfl, ?_⟩
    · exact hrp.ne' (pairing_eq_zero_of_inactive hz)
    · simpa only [f, rootForm_apply] using hrp
  have hpw (j : activeRoots R a) (hjp : 0 < f j p) : 0 ≤ f j w := by
    by_contra! hneg
    have := (hfixed j hneg.ne).1
    exact (not_lt_of_gt (mul_neg_of_pos_of_neg hjp hneg)) this
  have hqw (j : activeRoots R a) (hjq : 0 < f j q) : 0 ≤ f j w := by
    by_contra! hneg
    have := (hfixed j hneg.ne).2
    exact (not_lt_of_gt (mul_neg_of_pos_of_neg hjq hneg)) this
  have hvs : v ∈ simpleRoots a (posSet R (p : E)) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i,
      mem_posSet_iff.mpr ⟨(Finset.mem_filter.mp i.prop).1, by
        simpa only [f, rootForm_apply] using hip⟩, rfl⟩, ?_⟩
    rintro ⟨u, hu, z, hz, hv⟩
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j, rfl, hjp⟩ := hroot p hu'
    obtain ⟨k, rfl, hkp⟩ := hroot p hz'
    have hsum (x : a) : f i x = f j x + f k x := by
      change (innerₗ a v) x = (innerₗ a _) x + (innerₗ a _) x
      rw [hv, map_add, LinearMap.add_apply]
    have hjw : f j w = 0 := by linarith [hpw j hjp, hpw k hkp, hsum w]
    have h := hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjw, hjp⟩)
    linarith [hsum p]
  have hnvs : -v ∈ simpleRoots a (posSet R (q : E)) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨-(i : E),
      mem_posSet_neg_iff hR |>.mpr ⟨(Finset.mem_filter.mp i.prop).1, by
        simpa only [f, rootForm_apply] using hiq⟩, by
          change a.orthogonalProjectionOnto (-(i : E)) = -v
          rw [map_neg]
          rfl⟩, ?_⟩
    rintro ⟨u, hu, z, hz, hv⟩
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j, rfl, hjq⟩ := hroot q hu'
    obtain ⟨k, rfl, hkq⟩ := hroot q hz'
    have hs (x : a) : -f i x = f j x + f k x := by
      have hv' := congrArg (fun x : a => innerₗ a x) hv
      rw [map_neg, map_add] at hv'
      exact congrArg (fun g : Module.Dual ℝ a => g x) hv'
    have hjw : f j w = 0 := by linarith [hqw j hjq, hqw k hkq, hs w]
    have hkw : f k w = 0 := by linarith [hqw j hjq, hqw k hkq, hs w]
    have hpos (l : activeRoots R a) (hlw : f l w = 0) (hlq : 0 < f l q) :
        -(l : E) ∈ posSet R (p : E) := by
      apply (mem_posSet_neg_iff hR).mpr
      refine ⟨(Finset.mem_filter.mp l.prop).1, ?_⟩
      have hn := ((mul_neg_iff.mp (hflip l hlw)).resolve_left
        (fun hh => (not_lt_of_gt hlq) hh.2)).1
      simpa only [f, rootForm_apply] using hn
    have hv' : v = restrictedRoot a (-(j : E)) + restrictedRoot a (-(k : E)) := by
      simp only [restrictedRoot, map_neg]
      simpa only [restrictedRoot, neg_neg, neg_add_rev, add_comm] using congrArg Neg.neg hv
    exact (Finset.mem_filter.mp hvs).2 ⟨_, Finset.mem_image.mpr ⟨_, hpos j hjw hjq, rfl⟩,
      _, Finset.mem_image.mpr ⟨_, hpos k hkw hkq, rfl⟩, hv'⟩
  refine ⟨i, fun h => hkeep i h hiw, hvs, hnvs, fun x hx hn => ?_⟩
  have hx0 : restrictedRoot a x ≠ 0 := fun h => hn 0 (by rwa [zero_smul])
  let j : activeRoots R a := ⟨x, Finset.mem_filter.mpr ⟨hx, hx0⟩⟩
  have hjw : f j w ≠ 0 := by
    intro h
    obtain ⟨c, _, hc⟩ := hprop i j hiw h
    apply hn c
    have hform (t : a) : ⟪restrictedRoot a x - c • v, t⟫ = 0 := by
      rw [inner_sub_left, real_inner_smul_left, sub_eq_zero]
      exact congrArg (fun l : Module.Dual ℝ a => l t) hc
    exact sub_eq_zero.mp (inner_self_eq_zero.mp (hform _))
  have h₁ := (hfixed j hjw).1
  have h₂ := (hfixed j hjw).2
  simp only [mem_posSet_iff, hx, true_and]
  rw [← rootForm_apply j p, ← rootForm_apply j q]
  rcases lt_or_gt_of_ne hjw with hw | hw
  · exact iff_of_false (not_lt_of_gt (neg_of_mul_pos_left h₁ hw.le))
      (not_lt_of_gt (neg_of_mul_pos_left h₂ hw.le))
  · exact iff_of_true (pos_of_mul_pos_left h₁ hw.le) (pos_of_mul_pos_left h₂ hw.le)

/-- **Galleries avoiding protected walls.** Let `x` and `y` be regular points of `a₁` at which
every root satisfying `keep` and nonzero on `a₁` has the same sign. If the parameter `μ` vanishes
on the restriction to `a₁` of every other root that is nonzero on `a₁`, then the family takes the
same value at `μ` on the chambers of `x` and `y`. -/
theorem family_eq_of_protected_signs (hR : IsRootSet R)
    {c₁ : Finset E → StrongDual ℝ a₁ → ℂ} (hc₁ : IsFamily R a₁ c₁) (keep : E → Prop)
    {x y : E} (hx : IsRegular R a₁ x) (hy : IsRegular R a₁ y)
    (hprotect : ∀ r ∈ R, restrictedRoot a₁ r ≠ 0 → keep r → 0 < ⟪r, x⟫ * ⟪r, y⟫)
    (μ : StrongDual ℝ a₁)
    (hμ : ∀ r ∈ R, restrictedRoot a₁ r ≠ 0 → ¬ keep r → μ (restrictedRoot a₁ r) = 0) :
    c₁ (posSet R x) μ = c₁ (posSet R y) μ := by
  let x' : a₁ := ⟨x, hx.1⟩
  let y' : a₁ := ⟨y, hy.1⟩
  let f := rootForm (R := R) (a := a₁)
  let keep' (i : activeRoots R a₁) := keep (i : E)
  have hprotect' (i : activeRoots R a₁) (hi : keep' i) : 0 < f i x' * f i y' := by
    change 0 < rootForm i x' * rootForm i y'
    rw [rootForm_apply, rootForm_apply]
    exact hprotect _ (Finset.mem_filter.mp i.prop).1 (Finset.mem_filter.mp i.prop).2 hi
  have hgal := reflTransGen_chamberStep f keep' ((isRegular_iff_rootForm x').mp hx)
    ((isRegular_iff_rootForm y').mp hy) hprotect'
  change c₁ (posSet R (x' : E)) μ = c₁ (posSet R (y' : E)) μ
  have hstep (s t : a₁) (hst : ChamberStep f keep' s t) :
      c₁ (posSet R (s : E)) μ = c₁ (posSet R (t : E)) μ := by
    rcases hst with hsame | hwall
    · rw [posSet_eq_of_sameChamber hsame]
    · obtain ⟨i, hi, hadj⟩ := posSet_wall_adjacent hR keep' hwall
      have hs : posSet R (s : E) ∈ parabolics R a₁ := mem_parabolics_iff.mpr
        ⟨s, (isRegular_iff_rootForm s).mpr hwall.1, rfl⟩
      have ht : posSet R (t : E) ∈ parabolics R a₁ := mem_parabolics_iff.mpr
        ⟨t, (isRegular_iff_rootForm t).mpr hwall.2.1, rfl⟩
      exact hc₁.2 _ hs _ ht _ hadj μ
        (hμ _ (Finset.mem_filter.mp i.prop).1 (Finset.mem_filter.mp i.prop).2 hi)
  have hchain (z : a₁) (h : Relation.ReflTransGen (ChamberStep f keep') x' z) :
      c₁ (posSet R (x' : E)) μ = c₁ (posSet R (z : E)) μ := by
    induction h with
    | refl => rfl
    | tail _ hstep' ih => exact ih.trans (hstep _ _ hstep')
  exact hchain y' hgal

/-- Two fine chambers extending the same coarse chamber have equal family values at the
    extended parameter. -/
theorem family_eq_of_coarse_chamber (hR : IsRootSet R) (haa₁ : a ≤ a₁)
    {c₁ : Finset E → StrongDual ℝ a₁ → ℂ} (hc₁ : IsFamily R a₁ c₁)
    {P P₁ P₂ : Finset E} (hP : P ∈ parabolics R a)
    (hP₁ : P₁ ∈ parabolics R a₁) (hP₂ : P₂ ∈ parabolics R a₁)
    (h₁ : P ⊆ P₁) (h₂ : P ⊆ P₂) (Λ : StrongDual ℝ a) :
    c₁ P₁ (extendParam a a₁ Λ) = c₁ P₂ (extendParam a a₁ Λ) := by
  obtain ⟨p, hp, rfl⟩ := mem_parabolics_iff.mp hP
  obtain ⟨q₁, hq₁, rfl⟩ := mem_parabolics_iff.mp hP₁
  obtain ⟨q₂, hq₂, rfl⟩ := mem_parabolics_iff.mp hP₂
  apply family_eq_of_protected_signs hR hc₁ (fun r => restrictedRoot a r ≠ 0) hq₁ hq₂
  · intro r hRmem _ hi
    rcases lt_or_gt_of_ne (hp.2 _ hRmem hi) with hn | hpos
    · have hneg := (mem_posSet_neg_iff hR).mpr ⟨hRmem, hn⟩
      exact mul_pos_of_neg_of_neg ((mem_posSet_neg_iff hR).mp (h₁ hneg)).2
        ((mem_posSet_neg_iff hR).mp (h₂ hneg)).2
    · have hp' := mem_posSet_iff.mpr ⟨hRmem, hpos⟩
      exact mul_pos (mem_posSet_iff.mp (h₁ hp')).2 (mem_posSet_iff.mp (h₂ hp')).2
  · intro r _ _ hi
    have hzero : restrictedRoot a r = 0 := not_ne_iff.mp hi
    change Λ (restrictedRoot a (restrictedRoot a₁ r : E)) = 0
    rw [restrictedRoot_nested haa₁, hzero, map_zero]

/-- A fine chamber extending a coarse chamber can be found by a small perturbation in the fine
    space. -/
theorem exists_fine_parabolic_extension (haa₁ : a ≤ a₁) {P : Finset E}
    (hP : P ∈ parabolics R a) : ∃ P₁ ∈ parabolics R a₁, P ⊆ P₁ := by
  obtain ⟨p, hp, rfl⟩ := mem_parabolics_iff.mp hP
  let x : a₁ := ⟨p, haa₁ hp.1⟩
  let f := rootForm (R := R) (a := a₁)
  obtain ⟨y, hy, hsign⟩ := exists_regular_preserving_signs f (fun i => rootForm_ne_zero i) x
  refine ⟨posSet R (y : E), mem_parabolics_iff.mpr ⟨y, (isRegular_iff_rootForm y).mpr hy, rfl⟩, ?_⟩
  intro r hr
  obtain ⟨hr, hrp⟩ := mem_posSet_iff.mp hr
  have hr0 : restrictedRoot a₁ r ≠ 0 := fun hz => hrp.ne' (pairing_eq_zero_of_inactive (p := x) hz)
  let i : activeRoots R a₁ := ⟨r, Finset.mem_filter.mpr ⟨hr, hr0⟩⟩
  have hp' : 0 < f i x := by simpa only [f, rootForm_apply] using hrp
  exact mem_posSet_iff.mpr ⟨hr, by
    rw [← rootForm_apply i y]
    exact pos_of_mul_pos_right (hsign i hp'.ne') hp'.le⟩

/-- The chosen induced-family value can be evaluated using any extending fine chamber. -/
theorem inducedFamily_eq_of_extension (hR : IsRootSet R) (haa₁ : a ≤ a₁)
    {c₁ : Finset E → StrongDual ℝ a₁ → ℂ} (hc₁ : IsFamily R a₁ c₁)
    {P P₁ : Finset E} (hP : P ∈ parabolics R a) (hP₁ : P₁ ∈ parabolics R a₁)
    (h : P ⊆ P₁) (Λ : StrongDual ℝ a) :
    inducedFamily R a a₁ c₁ P Λ = c₁ P₁ (extendParam a a₁ Λ) := by
  have he : ∃ Q ∈ parabolics R a₁, P ⊆ Q := ⟨P₁, hP₁, h⟩
  simp only [inducedFamily, dite_eq_left he]
  exact family_eq_of_coarse_chamber hR haa₁ hc₁ hP he.choose_spec.1 hP₁ he.choose_spec.2 h Λ

end Langlands.GMFamily
