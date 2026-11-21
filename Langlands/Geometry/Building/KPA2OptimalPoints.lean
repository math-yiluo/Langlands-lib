import Langlands.Geometry.Building.KPOptimalPoints
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FinCases

/-! # The coordinate optimal-point calculation of KP Example 13.4.3 -/

noncomputable section

namespace Langlands.Geometry.Building.AffineRootSystem.A2Alcove

open GalleryGeometry Set SignType

/-- The three barycentric affine functionals `a`, `b` and `1-a-b`. -/
def coordinate : Fin 3 → ((ℝ × ℝ) →ᵃ[ℝ] ℝ) :=
  ![(LinearMap.fst ℝ ℝ ℝ).toAffineMap, (LinearMap.snd ℝ ℝ ℝ).toAffineMap,
    AffineMap.const ℝ (ℝ × ℝ) 1 - (LinearMap.fst ℝ ℝ ℝ).toAffineMap -
      (LinearMap.snd ℝ ℝ ℝ).toAffineMap]

@[simp] theorem coordinate_zero (x : ℝ × ℝ) : coordinate 0 x = x.1 := rfl
@[simp] theorem coordinate_one (x : ℝ × ℝ) : coordinate 1 x = x.2 := rfl
@[simp] theorem coordinate_two (x : ℝ × ℝ) : coordinate 2 x = 1 - x.1 - x.2 := rfl

@[simp] private theorem neg_coordinate_apply (i : Fin 3) (x : ℝ × ℝ) :
    (-coordinate i) x = -coordinate i x := rfl

/-- The complementary strip functional `1 - coordinate i`. -/
def complement (i : Fin 3) : (ℝ × ℝ) →ᵃ[ℝ] ℝ :=
  -coordinate i + AffineMap.const ℝ (ℝ × ℝ) 1

@[simp] theorem complement_apply (i : Fin 3) (x : ℝ × ℝ) :
    complement i x = 1 - coordinate i x := by change -coordinate i x + 1 = _; ring

private def translate (ψ : (ℝ × ℝ) →ᵃ[ℝ] ℝ) (n : ℤ) : (ℝ × ℝ) →ᵃ[ℝ] ℝ :=
  ψ + AffineMap.const ℝ (ℝ × ℝ) (n : ℝ)

@[simp] private theorem translate_apply (ψ : (ℝ × ℝ) →ᵃ[ℝ] ℝ) (n : ℤ) (x : ℝ × ℝ) :
    translate ψ n x = ψ x + (n : ℝ) := rfl

/-- The shifts by integers of the six directions `±a`, `±b`, `±(a+b)`, expressed in
barycentric affine coordinates. -/
def roots : Set ((ℝ × ℝ) →ᵃ[ℝ] ℝ) :=
  {ψ | ∃ (i : Fin 3) (n : ℤ), ψ = translate (coordinate i) n ∨ ψ = translate (-coordinate i) n}

private theorem coordinate_mem_roots (i : Fin 3) : coordinate i ∈ roots := by
  exact ⟨i, 0, Or.inl (AffineMap.ext fun x => by simp)⟩

private theorem complement_mem_roots (i : Fin 3) : complement i ∈ roots := by
  exact ⟨i, 1, Or.inr (AffineMap.ext fun x => by simp [sub_eq_add_neg, add_comm])⟩

/-- The interior representative with all three barycentric coordinates `1/3`. -/
def center : ℝ × ℝ := (1 / 3, 1 / 3)

@[simp] theorem coordinate_center (i : Fin 3) : coordinate i center = 1 / 3 := by
  fin_cases i <;> norm_num [center]

@[simp] theorem sum_coordinate (x : ℝ × ℝ) : ∑ i, coordinate i x = 1 := by
  rw [Fin.sum_univ_three, coordinate_zero, coordinate_one, coordinate_two]
  ring

private theorem one_mem_periods : (1 : ℝ) ∈ rationalRootPeriods roots := by
  refine ⟨zero_lt_one, ⟨1, Rat.cast_one⟩, ?_⟩
  rintro ψ ⟨i, n, rfl | rfl⟩
  · exact ⟨i, n+1, Or.inl (AffineMap.ext fun x => by
      change (coordinate i x + (n : ℝ)) + 1 = coordinate i x + ((n+1 : ℤ) : ℝ)
      push_cast; ring)⟩
  · exact ⟨i, n+1, Or.inr (AffineMap.ext fun x => by
      change (-coordinate i x + (n : ℝ)) + 1 = -coordinate i x + ((n+1 : ℤ) : ℝ)
      push_cast; ring)⟩

private theorem eval_origin_integer {ψ : (ℝ × ℝ) →ᵃ[ℝ] ℝ} (hψ : ψ ∈ roots) :
    ∃ n : ℤ, (n : ℝ) = ψ 0 := by
  obtain ⟨i, n, h | h⟩ := hψ
  · rw [h, translate_apply]
    fin_cases i
    · exact ⟨n, by simp⟩
    · exact ⟨n, by simp⟩
    · exact ⟨1+n, by simp⟩
  · rw [h, translate_apply, neg_coordinate_apply]
    fin_cases i
    · exact ⟨n, by simp⟩
    · exact ⟨n, by simp⟩
    · exact ⟨-1+n, by simp [sub_eq_add_neg]⟩

/-- The least positive rational period of the coordinate arrangement is one. -/
theorem rootPeriod_roots : rootPeriod roots = 1 := by
  apply rootPeriod_eq_of_isLeast
  refine ⟨one_mem_periods, fun t ht => ?_⟩
  obtain ⟨n, hn⟩ := eval_origin_integer (ht.2.2 _ (coordinate_mem_roots 0))
  change (n : ℝ) = 0 + t at hn
  rw [zero_add] at hn
  have hpos : (0 : ℤ) < n := by exact_mod_cast (hn.symm ▸ ht.1)
  rw [← hn]
  exact_mod_cast (show (1 : ℤ) ≤ n by omega)

private theorem int_cases (n : ℤ) : (n : ℝ) ≤ -1 ∨ (n : ℝ) = 0 ∨ 1 ≤ (n : ℝ) := by
  rcases lt_trichotomy n 0 with h | rfl | h
  · exact Or.inl (by exact_mod_cast (show n ≤ -1 by omega))
  · norm_num
  · exact Or.inr (Or.inr (by exact_mod_cast (show 1 ≤ n by omega)))

/-- The barycenter avoids all the affine root hyperplanes. -/
theorem regular_center : IsRegular roots center := by
  rintro ψ ⟨i, n, rfl | rfl⟩ <;>
    simp only [translate_apply, neg_coordinate_apply, coordinate_center] <;>
    rcases int_cases n with hn | hn | hn <;> linarith

private theorem coordinate_le_one_of_nonneg {x : ℝ × ℝ} (h : ∀ i, 0 ≤ coordinate i x)
    (i : Fin 3) : coordinate i x ≤ 1 := by
  calc
    coordinate i x ≤ ∑ j, coordinate j x :=
      Finset.single_le_sum (fun j _ => h j) (Finset.mem_univ i)
    _ = 1 := sum_coordinate x

private theorem sign_nonneg_or (u v : ℝ) (hu : 0 ≤ u) (hv : 0 < v) :
    sign u = 0 ∨ sign u = sign v := by
  rcases lt_or_eq_of_le hu with h | h
  · exact Or.inr ((sign_pos h).trans (sign_pos hv).symm)
  · exact Or.inl (sign_eq_zero_iff.mpr h.symm)

private theorem sign_nonpos_or (u v : ℝ) (hu : u ≤ 0) (hv : v < 0) :
    sign u = 0 ∨ sign u = sign v := by
  rcases lt_or_eq_of_le hu with h | h
  · exact Or.inr ((sign_neg h).trans (sign_neg hv).symm)
  · exact Or.inl (sign_eq_zero_iff.mpr h)

/-- The closed facet at the regular representative is the usual closed triangle. -/
theorem mem_facetClosure_center {x : ℝ × ℝ} :
    x ∈ facetClosure roots center ↔ ∀ i, 0 ≤ coordinate i x := by
  constructor
  · intro h i
    rcases h _ (coordinate_mem_roots i) with hzero | hpos
    · exact (sign_eq_zero_iff.mp hzero).ge
    · rw [coordinate_center, sign_pos (by norm_num : (0 : ℝ) < 1/3)] at hpos
      exact (sign_eq_one_iff.mp hpos).le
  · intro h ψ hψ
    obtain ⟨i, n, rfl | rfl⟩ := hψ
    · have h0 := h i
      have h1 := coordinate_le_one_of_nonneg h i
      simp only [translate_apply, coordinate_center]
      rcases int_cases n with hn | hn | hn
      · exact sign_nonpos_or _ _ (by linarith) (by linarith)
      · exact sign_nonneg_or _ _ (by linarith) (by linarith)
      · exact sign_nonneg_or _ _ (by linarith) (by linarith)
    · have h0 := h i
      have h1 := coordinate_le_one_of_nonneg h i
      simp only [translate_apply, neg_coordinate_apply, coordinate_center]
      rcases int_cases n with hn | hn | hn
      · exact sign_nonpos_or _ _ (by linarith) (by linarith)
      · exact sign_nonpos_or _ _ (by linarith) (by linarith)
      · exact sign_nonneg_or _ _ (by linarith) (by linarith)

private theorem mem_strip_of_eval_center {ψ : (ℝ × ℝ) →ᵃ[ℝ] ℝ} (hψ : ψ ∈ roots)
    (h0 : 0 < ψ center) (h1 : ψ center < 1) : ψ ∈ positiveRootsBelowPeriod roots center := by
  have hpos : ∀ y ∈ facet roots center, 0 < ψ y := fun y hy => by
    have he := hy ψ hψ
    rw [sign_pos h0, eq_comm, sign_eq_one_iff] at he
    exact he
  have hm : translate ψ (-1) ∈ roots := by
    obtain ⟨i, n, rfl | rfl⟩ := hψ
    · exact ⟨i, n-1, Or.inl (AffineMap.ext fun x => by simp; ring)⟩
    · exact ⟨i, n-1, Or.inr (AffineMap.ext fun x => by simp; ring)⟩
  refine ⟨⟨hψ, hpos⟩, fun y hy => ?_⟩
  have he := hy _ hm
  have hneg : translate ψ (-1) center < 0 := by simpa [sub_eq_add_neg] using sub_neg.mpr h1
  rw [sign_neg hneg, eq_comm, sign_eq_neg_one_iff] at he
  simpa [rootPeriod_roots, sub_eq_add_neg] using he

/-- The six strip roots are the barycentric coordinates and their complements. -/
theorem mem_positiveRootsBelowPeriod_center {ψ : (ℝ × ℝ) →ᵃ[ℝ] ℝ} :
    ψ ∈ positiveRootsBelowPeriod roots center ↔
      ∃ i, ψ = coordinate i ∨ ψ = complement i := by
  constructor
  · intro h
    have hval := mem_positiveRootsBelowPeriod_apply h
    rw [rootPeriod_roots] at hval
    obtain ⟨i, n, rfl | rfl⟩ := h.1.1
    · refine ⟨i, Or.inl (AffineMap.ext fun x => ?_)⟩
      simp only [translate_apply, coordinate_center] at hval
      have hn : (n : ℝ) = 0 := by rcases int_cases n with hn | hn | hn <;> linarith
      simp [hn]
    · refine ⟨i, Or.inr (AffineMap.ext fun x => ?_)⟩
      simp only [translate_apply, neg_coordinate_apply, coordinate_center] at hval
      have hn : (n : ℝ) = 1 := by
        rcases int_cases n with hn | hn | hn
        · linarith [hval.1]
        · linarith [hval.1]
        · have hlt : n < 2 := by exact_mod_cast (show (n : ℝ) < 2 by linarith [hval.2])
          exact_mod_cast (show n = 1 by
            have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
            omega)
      simp [hn, sub_eq_add_neg, add_comm]
  · rintro ⟨i, rfl | rfl⟩
    · exact mem_strip_of_eval_center (coordinate_mem_roots i) (by norm_num) (by norm_num)
    · exact mem_strip_of_eval_center (complement_mem_roots i) (by norm_num) (by norm_num)

private def weight (I : Finset (Fin 3)) (i : Fin 3) : ℚ :=
  if i ∈ I then 1 / (I.card : ℚ) else 0

/-- The equal-weight point on a face indexed by the nonempty set `I` of its vertices.
The seven nonempty subsets index the three vertices, three edge midpoints and barycenter. -/
def faceBarycenter (I : Finset (Fin 3)) : ℝ × ℝ := (weight I 0, weight I 1)

private theorem sum_weight {I : Finset (Fin 3)} (hI : I.Nonempty) : ∑ i, weight I i = 1 := by
  have hpos : (I.card : ℚ) ≠ 0 := by exact_mod_cast hI.card_ne_zero
  simp only [weight, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
    one_div, mul_inv_cancel₀ hpos]

private theorem coordinate_faceBarycenter_cast {I : Finset (Fin 3)} (hI : I.Nonempty) (i : Fin 3) :
    coordinate i (faceBarycenter I) = (weight I i : ℝ) := by
  fin_cases i
  · rfl
  · rfl
  · have h := sum_weight hI
    rw [Fin.sum_univ_three] at h
    have h' : (weight I 0 : ℝ) + weight I 1 + weight I 2 = 1 := by exact_mod_cast h
    change 1 - (weight I 0 : ℝ) - weight I 1 = weight I 2
    linarith

/-- On the face indexed by `I`, the barycenter gives each vertex of `I` equal weight. -/
theorem coordinate_faceBarycenter {I : Finset (Fin 3)} (hI : I.Nonempty) (i : Fin 3) :
    coordinate i (faceBarycenter I) = if i ∈ I then (1 : ℝ) / (I.card : ℝ) else (0 : ℝ) := by
  rw [coordinate_faceBarycenter_cast hI]
  by_cases hi : i ∈ I <;> simp [weight, hi]

private theorem faceBarycenter_mem {I : Finset (Fin 3)} (hI : I.Nonempty) :
    faceBarycenter I ∈ facetClosure roots center := by
  refine mem_facetClosure_center.2 fun i => ?_
  rw [coordinate_faceBarycenter hI]
  split_ifs <;> positivity

/-- Root rationality is equivalent to rationality of the two input coordinates. -/
theorem isRationalPoint_iff {x : ℝ × ℝ} : IsRationalPoint roots x ↔
    x.1 ∈ Set.range ((↑) : ℚ → ℝ) ∧ x.2 ∈ Set.range ((↑) : ℚ → ℝ) := by
  constructor
  · intro h
    exact ⟨h _ (coordinate_mem_roots 0), h _ (coordinate_mem_roots 1)⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have hcoord (i : Fin 3) : ∃ q : ℚ, (q : ℝ) = coordinate i x := by
      fin_cases i
      · exact ⟨a, ha⟩
      · exact ⟨b, hb⟩
      · exact ⟨1 - a - b, by simp [ha, hb]⟩
    rintro ψ ⟨i, n, rfl | rfl⟩
    · obtain ⟨q, hq⟩ := hcoord i
      exact ⟨q + n, by simp [hq]⟩
    · obtain ⟨q, hq⟩ := hcoord i
      exact ⟨-q + n, by simp [hq]⟩

private theorem faceBarycenter_rational (I : Finset (Fin 3)) :
    IsRationalPoint roots (faceBarycenter I) :=
  isRationalPoint_iff.2 ⟨⟨weight I 0, rfl⟩, ⟨weight I 1, rfl⟩⟩

private theorem coordinate_faceBarycenter_le {I : Finset (Fin 3)} (hI : I.Nonempty) (i : Fin 3) :
    coordinate i (faceBarycenter I) ≤ (1 : ℝ) / (I.card : ℝ) := by
  rw [coordinate_faceBarycenter hI]
  split_ifs
  · rfl
  · positivity

private theorem coordinate_faceBarycenter_of_mem {I : Finset (Fin 3)} (hI : I.Nonempty)
    {i : Fin 3} (hi : i ∈ I) :
    coordinate i (faceBarycenter I) = (1 : ℝ) / (I.card : ℝ) := by
  simp [coordinate_faceBarycenter hI, hi]

/-- The seven indicated points contain an optimizer for every nonempty subset of the
six strip roots of the coordinate alcove. -/
theorem exists_optimal_faceBarycenter {S : Finset ((ℝ × ℝ) →ᵃ[ℝ] ℝ)} (hS : S.Nonempty)
    (hsub : (↑S : Set _) ⊆ positiveRootsBelowPeriod roots center) :
    ∃ T : Finset (Fin 3), T.Nonempty ∧ IsOptimalPointFor roots center S (faceBarycenter T) := by
  classical
  let I := Finset.univ.filter (fun i : Fin 3 => coordinate i ∈ S)
  let J := Finset.univ.filter (fun j : Fin 3 => complement j ∈ S)
  have hI (i : Fin 3) : i ∈ I ↔ coordinate i ∈ S := by simp [I]
  have hJ (i : Fin 3) : i ∈ J ↔ complement i ∈ S := by simp [J]
  have hcases {ψ : (ℝ × ℝ) →ᵃ[ℝ] ℝ} (hψ : ψ ∈ S) :
      (∃ i ∈ I, ψ = coordinate i) ∨ ∃ j ∈ J, ψ = complement j := by
    obtain ⟨i, rfl | rfl⟩ := mem_positiveRootsBelowPeriod_center.1 (hsub hψ)
    · exact Or.inl ⟨i, (hI i).2 hψ, rfl⟩
    · exact Or.inr ⟨i, (hJ i).2 hψ, rfl⟩
  let f (x : ℝ × ℝ) := S.inf' hS (fun ψ => ψ x)
  have hf (x : ℝ × ℝ) {ψ : (ℝ × ℝ) →ᵃ[ℝ] ℝ} (hψ : ψ ∈ S) : f x ≤ ψ x := S.inf'_le _ hψ
  have hull (y : ℝ × ℝ) (hy : y ∈ facetClosure roots center) : f y ≤ 1 := by
    obtain ⟨ψ, hψ⟩ := hS
    have hny := mem_facetClosure_center.1 hy
    refine (hf y hψ).trans ?_
    rcases hcases hψ with ⟨i, -, rfl⟩ | ⟨j, -, rfl⟩
    · exact coordinate_le_one_of_nonneg hny i
    · simp only [complement_apply]; linarith [hny j]
  have finish (T : Finset (Fin 3)) (hT : T.Nonempty) (m : ℝ)
      (hup : ∀ y ∈ facetClosure roots center, f y ≤ m)
      (hlow : ∀ ψ ∈ S, m ≤ ψ (faceBarycenter T)) :
      ∃ T : Finset (Fin 3), T.Nonempty ∧ IsOptimalPointFor roots center S (faceBarycenter T) := by
    refine ⟨T, hT, regular_center, hS, hsub, faceBarycenter_mem hT, ?_, faceBarycenter_rational T⟩
    exact fun y hy => (hup y hy).trans ((S.le_inf'_iff hS _).2 hlow)
  by_cases hIempty : I = ∅
  · have hJonly {ψ : (ℝ × ℝ) →ᵃ[ℝ] ℝ} (hψ : ψ ∈ S) : ∃ j ∈ J, ψ = complement j := by
      rcases hcases hψ with ⟨i, hi, -⟩ | h
      · simp [hIempty] at hi
      · exact h
    by_cases hJall : J = Finset.univ
    · let T : Finset (Fin 3) := Finset.univ
      have hT : T.Nonempty := Finset.univ_nonempty
      have hor (i : Fin 3) : coordinate i (faceBarycenter T) = 1/3 := by
        rw [coordinate_faceBarycenter_of_mem hT (Finset.mem_univ i)]
        norm_num [T]
      refine finish T hT (2/3) (fun y hy => ?_) (fun ψ hψ => ?_)
      · have hsum := Finset.sum_le_sum (s := T) (fun j hj => hf y ((hJ j).1 (hJall.symm ▸ hj)))
        change (∑ _j ∈ T, f y) ≤ ∑ j ∈ T, complement j y at hsum
        simp only [T, complement_apply, Finset.sum_sub_distrib, Finset.sum_const, Fintype.card_fin,
          Finset.card_univ, nsmul_eq_mul, Nat.cast_ofNat, sum_coordinate, mul_one] at hsum
        linarith
      · obtain ⟨j, -, rfl⟩ := hJonly hψ
        rw [complement_apply, hor]
        norm_num
    · obtain ⟨i, hi⟩ : ∃ i : Fin 3, i ∉ J := by
        by_contra! h
        exact hJall (Finset.eq_univ_of_forall h)
      let T : Finset (Fin 3) := {i}
      have hT : T.Nonempty := Finset.singleton_nonempty i
      refine finish T hT 1 hull fun ψ hψ => ?_
      obtain ⟨j, hj, rfl⟩ := hJonly hψ
      have hji : j ∉ T := by
        intro hjT
        obtain rfl : j = i := Finset.mem_singleton.1 hjT
        exact hi hj
      simp [coordinate_faceBarycenter hT, hji]
  · have hIn : I.Nonempty := Finset.nonempty_iff_ne_empty.2 hIempty
    by_cases hIc : I.card = 1
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.1 hIc
      have hiI : i ∈ I := by simp [hi]
      by_cases hij : i ∈ J
      · have hne : i ≠ i+1 := by fin_cases i <;> decide
        let T : Finset (Fin 3) := {i, i+1}
        have hT : T.Nonempty := ⟨i, by simp [T]⟩
        have hTi : i ∈ T := by simp [T]
        have hcard : T.card = 2 := by simp [T, hne]
        refine finish T hT (1/2) (fun y hy => ?_) fun ψ hψ => ?_
        · have ha := hf y ((hI i).1 hiI)
          have hb := hf y ((hJ i).1 hij)
          rw [complement_apply] at hb
          linarith
        · rcases hcases hψ with ⟨j, hj, rfl⟩ | ⟨j, -, rfl⟩
          · have hji : j = i := Finset.mem_singleton.1 (hi ▸ hj)
            subst j
            simp [coordinate_faceBarycenter_of_mem hT hTi, hcard]
          · have hb := coordinate_faceBarycenter_le hT j
            rw [hcard] at hb
            push_cast at hb
            rw [complement_apply]
            linarith
      · let T : Finset (Fin 3) := {i}
        have hT : T.Nonempty := Finset.singleton_nonempty i
        refine finish T hT 1 hull fun ψ hψ => ?_
        rcases hcases hψ with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
        · have hji : j = i := Finset.mem_singleton.1 (hi ▸ hj)
          subst j
          simp [coordinate_faceBarycenter_of_mem hT (Finset.mem_singleton_self i), T]
        · have hji : j ∉ T := fun h => hij ((Finset.mem_singleton.1 h) ▸ hj)
          simp [coordinate_faceBarycenter hT, hji]
    · have hcard : 2 ≤ (I.card : ℝ) := by
        exact_mod_cast (show 2 ≤ I.card by have := hIn.card_pos; omega)
      have hm : (1 : ℝ) / I.card ≤ 1 / 2 := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < I.card)]
        linarith
      refine finish I hIn (1 / I.card) (fun y hy => ?_) fun ψ hψ => ?_
      · have hny := mem_facetClosure_center.1 hy
        have hsum : (∑ i ∈ I, coordinate i y) ≤ 1 := (sum_coordinate y) ▸
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I) (fun i _ _ => hny i)
        apply (le_div_iff₀ (by linarith : (0 : ℝ) < I.card)).2
        calc
          f y * I.card = ∑ _i ∈ I, f y := by simp [mul_comm]
          _ ≤ ∑ i ∈ I, coordinate i y := Finset.sum_le_sum fun i hi => hf y ((hI i).1 hi)
          _ ≤ 1 := hsum
      · rcases hcases hψ with ⟨i, hi, rfl⟩ | ⟨j, -, rfl⟩
        · rw [coordinate_faceBarycenter_of_mem hIn hi]
        · have hj := coordinate_faceBarycenter_le hIn j
          rw [complement_apply]
          linarith

open scoped Classical in
/-- A nonempty set of barycentric roots has its unique optimizer at the corresponding
face barycenter. This includes the two vertices, the opposite edge midpoint, and the
alcove barycenter in KP Example 13.4.3. -/
theorem isOptimalPointFor_coordinates_iff {x : ℝ × ℝ} {I : Finset (Fin 3)} (hI : I.Nonempty) :
    IsOptimalPointFor roots center (I.image coordinate) x ↔ x = faceBarycenter I := by
  constructor
  · intro h
    obtain ⟨-, -, -, hx, hmax, -⟩ := isOptimalPointFor_iff.1 h
    obtain ⟨ψ, hψ, hmin⟩ := hmax (faceBarycenter I) (faceBarycenter_mem hI)
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hψ
    have hle (i : Fin 3) : coordinate i (faceBarycenter I) ≤ coordinate i x := by
      by_cases hi : i ∈ I
      · rw [coordinate_faceBarycenter_of_mem hI hi, ← coordinate_faceBarycenter_of_mem hI hj]
        exact hmin _ (Finset.mem_image_of_mem _ hi)
      · simpa [coordinate_faceBarycenter hI, hi] using mem_facetClosure_center.1 hx i
    have heq (i : Fin 3) : coordinate i x = coordinate i (faceBarycenter I) := by
      apply le_antisymm _ (hle i)
      by_contra! hlt
      have hs : ∑ k, coordinate k (faceBarycenter I) < ∑ k, coordinate k x :=
        Finset.sum_lt_sum (fun k _ => hle k) ⟨i, Finset.mem_univ i, hlt⟩
      simp at hs
    exact Prod.ext (heq 0) (heq 1)
  · rintro rfl
    refine isOptimalPointFor_iff.2 ⟨regular_center, hI.image _, ?_, faceBarycenter_mem hI,
      ?_, faceBarycenter_rational I⟩
    · intro ψ hψ
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hψ
      exact mem_positiveRootsBelowPeriod_center.2 ⟨i, Or.inl rfl⟩
    · intro y hy
      have hn := mem_facetClosure_center.1 hy
      have hs : ∑ i ∈ I, coordinate i y ≤ 1 := (sum_coordinate y) ▸
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I) (fun i _ _ => hn i)
      have hcard : (I.card : ℝ) ≠ 0 := by exact_mod_cast hI.card_ne_zero
      have hm : ∃ i ∈ I, coordinate i y ≤ (1 : ℝ) / (I.card : ℝ) := by
        apply Finset.exists_le_of_sum_le hI (f := fun i => coordinate i y)
          (g := fun _ => (1 : ℝ) / (I.card : ℝ))
        simpa [nsmul_eq_mul, one_div, mul_inv_cancel₀ hcard] using hs
      obtain ⟨i, hi, hm⟩ := hm
      refine ⟨coordinate i, Finset.mem_image_of_mem _ hi, ?_⟩
      intro ψ hψ
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hψ
      rwa [coordinate_faceBarycenter_of_mem hI hk]

/-- The optimizers of a single complementary root are exactly the rational points of the
opposite edge. For `i = 2` the root is `a + b` in KP Example 13.4.3. -/
theorem isOptimalPointFor_complement_iff {x : ℝ × ℝ} (i : Fin 3) :
    IsOptimalPointFor roots center {complement i} x ↔
      x ∈ facetClosure roots center ∧ coordinate i x = 0 ∧ IsRationalPoint roots x := by
  have hmem := mem_positiveRootsBelowPeriod_center.2 ⟨i, Or.inr rfl⟩
  rw [isOptimalPointFor_singleton_iff]
  constructor
  · rintro ⟨-, -, hx, hmax, hrat⟩
    let T : Finset (Fin 3) := {i + 1}
    have hT : T.Nonempty := Finset.singleton_nonempty _
    have hi : i ∉ T := by fin_cases i <;> decide
    have hzero : coordinate i (faceBarycenter T) = 0 := by
      simp [coordinate_faceBarycenter hT, hi]
    have hopt := hmax (faceBarycenter T) (faceBarycenter_mem hT)
    simp only [complement_apply, hzero, sub_zero] at hopt
    exact ⟨hx, le_antisymm (by linarith) (mem_facetClosure_center.1 hx i), hrat⟩
  · rintro ⟨hx, hi, hrat⟩
    refine ⟨regular_center, hmem, hx, fun y hy => ?_, hrat⟩
    simp only [complement_apply, hi, sub_zero]
    linarith [mem_facetClosure_center.1 hy i]

private def nonemptyFaces : Finset (Finset (Fin 3)) := Finset.univ.powerset.erase ∅

private theorem mem_nonemptyFaces {I : Finset (Fin 3)} : I ∈ nonemptyFaces ↔ I.Nonempty := by
  simp [nonemptyFaces, Finset.nonempty_iff_ne_empty]

open scoped Classical in
/-- The three vertices, three edge midpoints, and the center of the coordinate alcove. -/
def faceBarycenters : Finset (ℝ × ℝ) := nonemptyFaces.image faceBarycenter

/-- The indicated seven coordinate points are distinct. -/
theorem card_faceBarycenters : faceBarycenters.card = 7 := by
  classical
  have hinj : Set.InjOn faceBarycenter ↑nonemptyFaces := by
    intro I hI J hJ h
    have support {K : Finset (Fin 3)} (hK : K.Nonempty) (i : Fin 3) :
        i ∈ K ↔ 0 < coordinate i (faceBarycenter K) := by
      rw [coordinate_faceBarycenter hK]
      by_cases hi : i ∈ K
      · simp [hi, hK]
      · simp [hi]
    ext i
    rw [support (mem_nonemptyFaces.1 hI), support (mem_nonemptyFaces.1 hJ), h]
  rw [faceBarycenters, Finset.card_image_iff.2 hinj]
  rw [nonemptyFaces, Finset.card_erase_of_mem (by simp), Finset.card_powerset]
  norm_num

/-- The fixed seven-point set meets the optimizer set for every nonempty subset of `Σ`. -/
theorem exists_optimal_mem_faceBarycenters {S : Finset ((ℝ × ℝ) →ᵃ[ℝ] ℝ)} (hS : S.Nonempty)
    (hsub : (↑S : Set _) ⊆ positiveRootsBelowPeriod roots center) :
    ∃ x ∈ faceBarycenters, IsOptimalPointFor roots center S x := by
  classical
  obtain ⟨T, hT, h⟩ := exists_optimal_faceBarycenter hS hsub
  exact ⟨faceBarycenter T, Finset.mem_image_of_mem _ (mem_nonemptyFaces.2 hT), h⟩

end Langlands.Geometry.Building.AffineRootSystem.A2Alcove
