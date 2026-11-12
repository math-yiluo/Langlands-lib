import Langlands.LinearAlgebra.FiniteHyperplaneSegment
import Langlands.LinearAlgebra.FiniteHyperplaneGallery

/-! # Finite galleries of rational sign chambers -/

noncomputable section

namespace Langlands.LinearAlgebra.FiniteHyperplaneSegment

variable {ι V : Type*} [Finite ι] [AddCommGroup V] [Module ℚ V]

/-- The unique possible zero parameter of a form along a regular-start segment. -/
def crossingTime (f : Module.Dual ℚ V) (x y : V) : ℚ :=
  f x / (f x - f y)

theorem apply_segment_formula (f : Module.Dual ℚ V) (x y : V) (t : ℚ) :
    f (segment x y t) = f x + t * (f y - f x) := by
  simp only [segment, map_add, map_smul, smul_eq_mul]
  ring

theorem eq_crossingTime_of_apply_segment_eq_zero (f : Module.Dual ℚ V)
    {x y : V} (hx : f x ≠ 0) {t : ℚ} (ht : f (segment x y t) = 0) :
    t = crossingTime f x y := by
  rw [apply_segment_formula] at ht
  have hden : f x - f y ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    exact hx (by simpa [he] using ht)
  apply (eq_div_iff hden).mpr
  nlinarith

theorem apply_segment_crossingTime_eq_zero (f : Module.Dual ℚ V)
    {x y : V} (hden : f x - f y ≠ 0) :
    f (segment x y (crossingTime f x y)) = 0 := by
  rw [apply_segment_formula]
  have h := div_mul_cancel₀ (f x) hden
  dsimp [crossingTime]
  nlinarith

/-- Opposite strict signs of an affine rational function give an interior zero. -/
theorem exists_affine_zero_between {A B a b : ℚ}
    (hab : a < b) (h : (A + a * B) * (A + b * B) < 0) :
    ∃ t : ℚ, a < t ∧ t < b ∧ A + t * B = 0 := by
  rcases mul_neg_iff.mp h with h | h
  · have hB : B < 0 := by nlinarith
    refine ⟨-A / B, (lt_div_iff_of_neg hB).mpr ?_,
      (div_lt_iff_of_neg hB).mpr ?_, ?_⟩
    · linarith [h.1]
    · linarith [h.2]
    · rw [div_mul_cancel₀ _ (ne_of_lt hB)]
      ring
  · have hB : 0 < B := by nlinarith
    refine ⟨-A / B, (lt_div_iff₀ hB).mpr ?_,
      (div_lt_iff₀ hB).mpr ?_, ?_⟩
    · linarith [h.1]
    · linarith [h.2]
    · rw [div_mul_cancel₀ _ (ne_of_gt hB)]
      ring

theorem exists_segment_zero_between (f : Module.Dual ℚ V) {x y : V}
    {a b : ℚ} (hab : a < b)
    (h : f (segment x y a) * f (segment x y b) < 0) :
    ∃ t : ℚ, a < t ∧ t < b ∧ f (segment x y t) = 0 := by
  simp only [apply_segment_formula] at h ⊢
  exact exists_affine_zero_between hab h

theorem mul_pos_of_no_segment_zero_between (f : Module.Dual ℚ V) {x y : V}
    {a b : ℚ} (hab : a < b)
    (ha : f (segment x y a) ≠ 0) (hb : f (segment x y b) ≠ 0)
    (hzero : ∀ t, a < t → t < b → f (segment x y t) ≠ 0) :
    0 < f (segment x y a) * f (segment x y b) := by
  by_contra h
  have hneg : f (segment x y a) * f (segment x y b) < 0 :=
    lt_of_le_of_ne (le_of_not_gt h) (mul_ne_zero ha hb)
  obtain ⟨t, hat, htb, ht⟩ := exists_segment_zero_between f hab hneg
  exact hzero t hat htb ht

theorem mul_neg_of_segment_zero_between (f : Module.Dual ℚ V) {x y : V}
    {a b t : ℚ} (hat : a < t) (htb : t < b)
    (ha : f (segment x y a) ≠ 0) (ht : f (segment x y t) = 0) :
    f (segment x y a) * f (segment x y b) < 0 := by
  have he (r : ℚ) : f (segment x y r) = (r - t) * (f y - f x) := by
    rw [apply_segment_formula] at ht ⊢
    nlinarith
  have hp : f y - f x ≠ 0 := by
    intro h
    exact ha (by rw [he, h, mul_zero])
  rw [he a, he b]
  have heq : (a - t) * (f y - f x) * ((b - t) * (f y - f x)) =
      ((a - t) * (b - t)) * (f y - f x) ^ 2 := by ring
  rw [heq]
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (sub_neg.mpr hat) (sub_pos.mpr htb))
    (sq_pos_of_ne_zero hp)

/-- The possible crossings strictly inside the unit interval. -/
def crossingTimes (f : ι → Module.Dual ℚ V) (x y : V) : Finset ℚ := by
  classical
  letI := Fintype.ofFinite ι
  exact (Finset.univ.image (fun i => crossingTime (f i) x y)).filter
    (fun t => 0 < t ∧ t < 1)

theorem mem_crossingTimes_iff (f : ι → Module.Dual ℚ V) (x y : V) (t : ℚ) :
    t ∈ crossingTimes f x y ↔
      (0 < t ∧ t < 1) ∧ ∃ i, crossingTime (f i) x y = t := by
  classical
  simp only [crossingTimes, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
    true_and]
  tauto

theorem mem_crossingTimes_of_segment_eq_zero (f : ι → Module.Dual ℚ V)
    {x y : V} (hx : Regular f x) {t : ℚ} (ht : 0 < t) (ht' : t < 1)
    {i : ι} (hi : f i (segment x y t) = 0) :
    t ∈ crossingTimes f x y :=
  (mem_crossingTimes_iff f x y t).mpr
    ⟨⟨ht, ht'⟩, i, (eq_crossingTime_of_apply_segment_eq_zero (f i) (hx i) hi).symm⟩

theorem exists_zero_of_mem_crossingTimes (f : ι → Module.Dual ℚ V)
    {x y : V} {t : ℚ} (ht : t ∈ crossingTimes f x y) :
    ∃ i, f i (segment x y t) = 0 := by
  obtain ⟨⟨ht0, -⟩, i, hi⟩ := (mem_crossingTimes_iff f x y t).mp ht
  have hden : f i x - f i y ≠ 0 := by
    intro h
    have : t = 0 := by simpa [crossingTime, h] using hi.symm
    exact (ne_of_gt ht0) this
  rw [← hi]
  exact ⟨i, apply_segment_crossingTime_eq_zero (f i) hden⟩

theorem regular_segment_of_not_mem_crossingTimes (f : ι → Module.Dual ℚ V)
    {x y : V} (hx : Regular f x) (hy : Regular f y) {t : ℚ}
    (ht : 0 ≤ t) (ht' : t ≤ 1) (hnot : t ∉ crossingTimes f x y) :
    Regular f (segment x y t) := by
  intro i hi
  by_cases ht0 : t = 0
  · exact hx i (by simpa [segment, ht0] using hi)
  by_cases ht1 : t = 1
  · exact hy i (by simpa [segment, ht1] using hi)
  exact hnot (mem_crossingTimes_of_segment_eq_zero f hx
    (lt_of_le_of_ne ht (Ne.symm ht0)) (lt_of_le_of_ne ht' ht1) hi)

/-- An actual rational wall witness, with all vanishing forms proportional.
The predicate `keep` specifies forms whose walls must be avoided. -/
def WallAdjacent (f : ι → Module.Dual ℚ V) (keep : ι → Prop) (x y : V) : Prop :=
  Regular f x ∧ Regular f y ∧ ∃ w : V,
    (∃ i, f i w = 0) ∧
    (∀ i, f i w = 0 → f i x * f i y < 0) ∧
    (∀ i, f i w ≠ 0 → 0 < f i x * f i w ∧ 0 < f i y * f i w) ∧
    (∀ i j, f i w = 0 → f j w = 0 → ∃ c : ℚ, c ≠ 0 ∧ f j = c • f i) ∧
    (∀ i, keep i → f i w ≠ 0)

/-- A chamber step either preserves all signs or crosses a single wall class. -/
def ChamberStep (f : ι → Module.Dual ℚ V) (keep : ι → Prop) (x y : V) : Prop :=
  SameChamber f x y ∨ WallAdjacent f keep x y

theorem regular_away_from_unique_crossing (f : ι → Module.Dual ℚ V)
    {x y : V} (hx : Regular f x) {a b t : ℚ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (ht : t ∈ (crossingTimes f x y).filter (fun r => a < r ∧ r < b))
    (hs : SparseInterval (crossingTimes f x y) a b) :
    ∀ r, a < r → r < b → r ≠ t → Regular f (segment x y r) := by
  classical
  intro r har hrb hrt i hi
  have hr : r ∈ (crossingTimes f x y).filter (fun r => a < r ∧ r < b) :=
    Finset.mem_filter.mpr ⟨mem_crossingTimes_of_segment_eq_zero f hx
      (lt_of_le_of_lt ha har) (lt_of_lt_of_le hrb hb) hi, har, hrb⟩
  exact hrt (Finset.card_le_one_iff.mp hs hr ht)

theorem chamberStep_of_sparse_interval (f : ι → Module.Dual ℚ V)
    (keep : ι → Prop) {x y : V} (hx : Regular f x) (hy : Regular f y)
    (hprop : ∀ (t : ℚ) (i j : ι), f i (segment x y t) = 0 →
      f j (segment x y t) = 0 → ∃ c : ℚ, c ≠ 0 ∧ f j = c • f i)
    (hprotect : ∀ i, keep i → 0 < f i x * f i y)
    {a b : ℚ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (ha' : a ∉ crossingTimes f x y) (hb' : b ∉ crossingTimes f x y)
    (hs : SparseInterval (crossingTimes f x y) a b) :
    ChamberStep f keep (segment x y a) (segment x y b) := by
  classical
  have hrega := regular_segment_of_not_mem_crossingTimes f hx hy
    ha (hab.le.trans hb) ha'
  have hregb := regular_segment_of_not_mem_crossingTimes f hx hy
    (ha.trans hab.le) hb hb'
  by_cases hne : ((crossingTimes f x y).filter (fun t => a < t ∧ t < b)).Nonempty
  · obtain ⟨t, ht⟩ := hne
    have hts := Finset.mem_filter.mp ht
    have hregular := regular_away_from_unique_crossing f hx ha hb ht hs
    right
    refine ⟨hrega, hregb, segment x y t, exists_zero_of_mem_crossingTimes f hts.1,
      ?_, ?_, hprop t, ?_⟩
    · intro i hi
      exact mul_neg_of_segment_zero_between (f i) hts.2.1 hts.2.2 (hrega i) hi
    · intro i hi
      constructor
      · apply mul_pos_of_no_segment_zero_between (f i) hts.2.1 (hrega i) hi
        intro r har hrt
        exact hregular r har (hrt.trans hts.2.2) (ne_of_lt hrt) i
      · have h := mul_pos_of_no_segment_zero_between (f i) hts.2.2 hi (hregb i)
          (fun r htr hrb =>
            hregular r (hts.2.1.trans htr) hrb (ne_of_gt htr) i)
        simpa only [mul_comm] using h
    · intro i hi
      exact apply_segment_ne_zero_of_mul_pos (f i) (hprotect i hi)
        ((mem_crossingTimes_iff f x y t).mp hts.1).1.1.le
        ((mem_crossingTimes_iff f x y t).mp hts.1).1.2.le
  · left
    intro i
    apply mul_pos_of_no_segment_zero_between (f i) hab (hrega i) (hregb i)
    intro t hat htb hi
    exact hne ⟨t, Finset.mem_filter.mpr
      ⟨mem_crossingTimes_of_segment_eq_zero f hx
        (lt_of_le_of_lt ha hat) (lt_of_lt_of_le htb hb) hi, hat, htb⟩⟩

theorem reflTransGen_chamberStep_of_generic (f : ι → Module.Dual ℚ V)
    (keep : ι → Prop) {x y : V} (hx : Regular f x) (hy : Regular f y)
    (hprop : ∀ (t : ℚ) (i j : ι), f i (segment x y t) = 0 →
      f j (segment x y t) = 0 → ∃ c : ℚ, c ≠ 0 ∧ f j = c • f i)
    (hprotect : ∀ i, keep i → 0 < f i x * f i y) :
    Relation.ReflTransGen (ChamberStep f keep) x y := by
  let R : ℚ → ℚ → Prop := fun a b =>
    ChamberStep f keep (segment x y a) (segment x y b)
  have hchain : Relation.ReflTransGen R 0 1 :=
    reflTransGen_of_sparse_intervals R (crossingTimes f x y) (by norm_num)
      (fun t ht => ((mem_crossingTimes_iff f x y t).mp ht).1)
      (fun _ _ ha hab hb ha' hb' hs =>
        chamberStep_of_sparse_interval f keep hx hy hprop hprotect
          ha hab hb ha' hb' hs)
  have h := Relation.ReflTransGen.lift (segment x y)
    (p := ChamberStep f keep) (fun _ _ h => h) 0 1 hchain
  change Relation.ReflTransGen (ChamberStep f keep) (segment x y 0) (segment x y 1) at h
  simpa [segment] using h

omit [Finite ι] in
theorem sameChamber_symm (f : ι → Module.Dual ℚ V) {x y : V}
    (h : SameChamber f x y) : SameChamber f y x := by
  intro i
  simpa only [mul_comm] using h i

omit [Finite ι] in
theorem sameChamber_trans (f : ι → Module.Dual ℚ V) {x y z : V}
    (hxy : SameChamber f x y) (hyz : SameChamber f y z) :
    SameChamber f x z := by
  intro i
  rcases mul_pos_iff.mp (hxy i) with h | h
  · rcases mul_pos_iff.mp (hyz i) with h' | h'
    · exact mul_pos h.1 h'.2
    · linarith [h.2, h'.1]
  · rcases mul_pos_iff.mp (hyz i) with h' | h'
    · linarith [h.2, h'.1]
    · exact mul_pos_of_neg_of_neg h.1 h'.2

/-- Any two regular rational vectors are joined by a finite sequence of chamber
and wall steps, avoiding every keep wall on which their signs agree. -/
theorem reflTransGen_chamberStep (f : ι → Module.Dual ℚ V)
    (keep : ι → Prop) {x y : V} (hx : Regular f x) (hy : Regular f y)
    (hprotect : ∀ i, keep i → 0 < f i x * f i y) :
    Relation.ReflTransGen (ChamberStep f keep) x y := by
  obtain ⟨z, hz, hsame, hprop⟩ := exists_segment_with_proportional_crossings f hx hy
  have hp : ∀ i, keep i → 0 < f i x * f i z := by
    intro i hi
    rcases mul_pos_iff.mp (hprotect i hi) with h | h
    · rcases mul_pos_iff.mp (hsame i) with h' | h'
      · exact mul_pos h.1 h'.2
      · linarith [h.2, h'.1]
    · rcases mul_pos_iff.mp (hsame i) with h' | h'
      · linarith [h.2, h'.1]
      · exact mul_pos_of_neg_of_neg h.1 h'.2
  exact (reflTransGen_chamberStep_of_generic f keep hx hz hprop hp).tail
    (Or.inl (sameChamber_symm f hsame))

end Langlands.LinearAlgebra.FiniteHyperplaneSegment
