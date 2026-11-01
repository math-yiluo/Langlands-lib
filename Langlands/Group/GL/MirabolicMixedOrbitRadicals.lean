import Langlands.Group.GL.MirabolicMixedOrbitData

/-! Elementary radical calculations for the actual mixed-orbit representatives. -/

namespace Langlands.GeneralLinear.Mirabolic.MixedOrbit

open Langlands.GeneralLinear.Mirabolic.MixedProduct

universe u

section Cycle

variable (t a : ℕ) (ha : a ≤ t)

/-- The source's descending cycle on the translation coordinates. -/
def cycleRadicalIndex (i : Fin (t + 1)) : Fin (t + 1) :=
  ⟨if i.val = a then t else if a < i.val then i.val - 1 else i.val, by
    have := i.isLt
    split_ifs <;> omega⟩

theorem descendingCycle_castSucc (i : Fin (t + 1)) :
    descendingCycle t a ha i.castSucc = (cycleRadicalIndex t a i).castSucc := by
  apply Fin.ext
  change (if i.val = a then t else if a < i.val ∧ i.val ≤ t then i.val - 1 else i.val) =
    if i.val = a then t else if a < i.val then i.val - 1 else i.val
  have := i.isLt
  split_ifs <;> omega

variable (R : Type u) [CommRing R]

/-- Inverse conjugation by the actual cycle permutes both matrix indices
by the descending cycle itself. -/
theorem cycleElement_inv_conjugate_entry (g : mirabolic (t + 1) R)
    (i j : Fin (t + 2)) :
    ((cycleElement t a ha R)⁻¹ * g * cycleElement t a ha R).val.val i j =
      g.val.val (descendingCycle t a ha i) (descendingCycle t a ha j) := by
  change ((permutation (t + 2) R (descendingCycle t a ha))⁻¹ * g.val *
    permutation (t + 2) R (descendingCycle t a ha)).val i j = _
  rw [mul_permutation_entry, permutation_inv, permutation_mul_entry]
  rfl

/-- The radical column after inverse conjugation by the source cycle. -/
theorem cycleElement_inv_conjugate_radicalElement (v : Fin (t + 1) → R) :
    (cycleElement t a ha R)⁻¹ * (radicalElement v).val * cycleElement t a ha R =
      (radicalElement (fun i => v (cycleRadicalIndex t a i))).val := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [cycleElement_inv_conjugate_entry]
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [descendingCycle_last]
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [descendingCycle_last, radicalElement_bottom, radicalElement_bottom]
    · rw [descendingCycle_castSucc, radicalElement_last, radicalElement_last]
  · rw [descendingCycle_castSucc, radicalElement_first, radicalElement_first]
    simp only [← descendingCycle_castSucc t a ha j, Equiv.apply_eq_iff_eq]

end Cycle

section RankCast

variable {R : Type u} [CommRing R] {m n : ℕ}

/-- Reindexing the rank transports the actual radical column by `Fin.cast`. -/
theorem rankCast_radicalElement (h : m = n) (v : Fin m → R) :
    rankCast h (radicalElement v).val =
      (radicalElement (fun i => v (Fin.cast h.symm i))).val := by
  subst h
  apply Subtype.ext
  apply Units.ext
  ext i j
  rfl

theorem rankCast_symm_radicalElement (h : m = n) (v : Fin n → R) :
    (rankCast h).symm (radicalElement v).val =
      (radicalElement (fun i => v (Fin.cast h i))).val := by
  subst h
  apply Subtype.ext
  apply Units.ext
  ext i j
  rfl

end RankCast

section MixedRadical

variable {R : Type u} [CommRing R] {k r : ℕ}

private theorem leftIndex_first (i : Fin k) :
    leftIndex k r (Sum.inl i) = (⟨i.val, by omega⟩ : Fin (k + r)).castSucc := by
  apply Fin.ext
  simp

private theorem leftIndex_second (i : Fin r) :
    leftIndex k r (Sum.inr i.castSucc) =
      (⟨k + i.val, by omega⟩ : Fin (k + r)).castSucc := by
  apply Fin.ext
  simp

private theorem rightIndex_first (i : Fin r) :
    rightIndex k r (Sum.inl i.castSucc) =
      (⟨i.val, by omega⟩ : Fin (k + r)).castSucc := by
  apply Fin.ext
  simp

private theorem rightIndex_middle (i : Fin k) :
    rightIndex k r (Sum.inr i) =
      (⟨r + i.val, by omega⟩ : Fin (k + r)).castSucc := by
  apply Fin.ext
  simp

/-- Every translation column belongs to the left mixed subgroup. -/
theorem radicalElement_mem_leftSubgroup (v : Fin (k + r) → R) :
    (radicalElement v).val ∈ leftSubgroup k r R := by
  rw [mem_leftSubgroup_iff_entry]
  intro i j
  rw [leftIndex_first, radicalElement_first]
  apply ite_eq_right
  intro he
  have he' := congrArg Fin.val he
  simp only [leftIndex_inr_val, Fin.val_castSucc] at he'
  change k + i.val = j.val at he'
  omega

/-- The left coefficient retains the tail of the translation column. -/
theorem leftProjection_radicalElement (v : Fin (k + r) → R)
    (hv : (radicalElement v).val ∈ leftSubgroup k r R) :
    leftProjection ⟨(radicalElement v).val, hv⟩ =
      (1, (radicalElement (fun i : Fin r => v ⟨k + i.val, by omega⟩)).val) := by
  apply Prod.ext
  · apply Units.ext
    ext i j
    change (leftProjection ⟨(radicalElement v).val, hv⟩).1.val i j =
      (1 : Matrix (Fin k) (Fin k) R) i j
    rw [leftProjection_gl_apply, leftIndex_first, leftIndex_first, radicalElement_first]
    simp only [Matrix.one_apply, Fin.ext_iff, Fin.val_castSucc]
  · apply Subtype.ext
    apply Units.ext
    ext i j
    rw [leftProjection_mirabolic_apply]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [leftIndex_last]
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [leftIndex_last, radicalElement_bottom, ↓reduceIte]
      · rw [leftIndex_second, radicalElement_last, radicalElement_last]
    · rw [leftIndex_second, radicalElement_first, radicalElement_first]
      congr 1
      apply propext
      constructor
      · intro he
        have he' : leftIndex k r (Sum.inr i) =
            leftIndex k r (Sum.inr j.castSucc) :=
          he.trans (leftIndex_second j).symm
        exact Sum.inr.inj ((leftIndex k r).injective he')
      · intro he
        subst i
        exact leftIndex_second j

/-- The right subgroup requires all middle-block translation coordinates to vanish. -/
theorem radicalElement_mem_rightSubgroup_iff (v : Fin (k + r) → R) :
    (radicalElement v).val ∈ rightSubgroup k r R ↔
      ∀ i : Fin k, v ⟨r + i.val, by omega⟩ = 0 := by
  constructor
  · intro hv i
    have he := (mem_rightSubgroup_iff_entry _).mp hv i (Fin.last r)
    simpa only [rightIndex_last, rightIndex_middle, radicalElement_last] using he
  · intro hv
    rw [mem_rightSubgroup_iff_entry]
    intro i j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [rightIndex_last, rightIndex_middle, radicalElement_last] using hv i
    · rw [rightIndex_first, rightIndex_middle, radicalElement_first]
      apply ite_eq_right
      intro he
      have he' := congrArg Fin.val he
      change r + i.val = j.val at he'
      omega

/-- The right coefficient retains the initial translation column. -/
theorem rightProjection_radicalElement (v : Fin (k + r) → R)
    (hv : (radicalElement v).val ∈ rightSubgroup k r R) :
    rightProjection ⟨(radicalElement v).val, hv⟩ =
      ((radicalElement (fun i : Fin r => v ⟨i.val, by omega⟩)).val, 1) := by
  apply Prod.ext
  · apply Subtype.ext
    apply Units.ext
    ext i j
    rw [rightProjection_mirabolic_apply]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [rightIndex_last]
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [rightIndex_last, radicalElement_bottom, ↓reduceIte]
      · rw [rightIndex_first, radicalElement_last, radicalElement_last]
    · rw [rightIndex_first, radicalElement_first, radicalElement_first]
      congr 1
      apply propext
      constructor
      · intro he
        have he' : rightIndex k r (Sum.inl i) =
            rightIndex k r (Sum.inl j.castSucc) :=
          he.trans (rightIndex_first j).symm
        exact Sum.inl.inj ((rightIndex k r).injective he')
      · intro he
        subst i
        exact rightIndex_first j
  · apply Units.ext
    ext i j
    change (rightProjection ⟨(radicalElement v).val, hv⟩).2.val i j =
      (1 : Matrix (Fin k) (Fin k) R) i j
    rw [rightProjection_gl_apply, rightIndex_middle, rightIndex_middle,
      radicalElement_first]
    simp only [Matrix.one_apply, Fin.ext_iff, Fin.val_castSucc,
      Nat.add_left_cancel_iff]

end MixedRadical

section LeftOrbit

variable (k r : ℕ) {R : Type u} [CommRing R]

/-- The translation column in the original left mixed coordinates after
inverse conjugation by representative `i` and rank transport. -/
def leftRadicalColumn (i : Fin 2) (v : Fin (k + r + 2) → R)
    (j : Fin (k + 1 + (r + 1))) : R :=
  if i = 0 then
    v (cycleRadicalIndex (k + r + 1) k (Fin.cast (totalRank_eq k r) j))
  else v (Fin.cast (totalRank_eq k r) j)

/-- Inverse conjugation and rank transport of a radical element at either
actual left representative. -/
theorem left_conjugate_radicalElement (i : Fin 2) (v : Fin (k + r + 2) → R) :
    (rankCast (totalRank_eq k r)).symm
        ((leftRepresentative k r R i)⁻¹ * (radicalElement v).val *
          leftRepresentative k r R i) =
      (radicalElement (leftRadicalColumn k r i v)).val := by
  fin_cases i
  · change (rankCast (totalRank_eq k r)).symm
      ((leftRepresentative k r R 0)⁻¹ * (radicalElement v).val *
        leftRepresentative k r R 0) =
      (radicalElement (leftRadicalColumn k r 0 v)).val
    rw [leftRepresentative_zero]
    change (rankCast (totalRank_eq k r)).symm
      ((cycleElement (k + r + 1) k (by omega) R)⁻¹ * (radicalElement v).val *
        cycleElement (k + r + 1) k (by omega) R) = _
    rw [cycleElement_inv_conjugate_radicalElement, rankCast_symm_radicalElement]
    rfl
  · change (rankCast (totalRank_eq k r)).symm
      ((leftRepresentative k r R 1)⁻¹ * (radicalElement v).val *
        leftRepresentative k r R 1) =
      (radicalElement (leftRadicalColumn k r 1 v)).val
    simp only [leftRepresentative_one, inv_one, one_mul, mul_one,
      rankCast_symm_radicalElement]
    rfl

/-- Every radical element lies in both actual left orbit stabilizers. -/
theorem radicalElement_mem_leftRadicalIntersection (i : Fin 2)
    (v : Fin (k + r + 2) → R) :
    radicalElement v ∈ leftRadicalIntersection k r R i := by
  rw [mem_radicalIntersection_iff, mem_leftInducing_iff, left_conjugate_radicalElement]
  exact radicalElement_mem_leftSubgroup _

/-- The actual radical element, valued in the left radical intersection. -/
def leftOrbitRadicalElement (i : Fin 2) (v : Fin (k + r + 2) → R) :
    leftRadicalIntersection k r R i :=
  ⟨radicalElement v, radicalElement_mem_leftRadicalIntersection k r i v⟩

/-- The exact coefficient of a translation at either actual left representative. -/
theorem leftRadicalCoefficient_element (i : Fin 2) (v : Fin (k + r + 2) → R) :
    leftRadicalCoefficient k r R i (leftOrbitRadicalElement k r i v) =
      (1, (radicalElement (fun j : Fin (r + 1) =>
        leftRadicalColumn k r i v ⟨k + 1 + j.val, by omega⟩)).val) := by
  let z := (leftInducingHom k r R)
    (Langlands.Geometric.stabilizerToInducing (leftInducing k r R)
      (plusSubgroup (k + r + 1) R) (leftRepresentative k r R i)
      (leftRadicalInclusion k r R i (leftOrbitRadicalElement k r i v)))
  have hz : z.val = (radicalElement (leftRadicalColumn k r i v)).val := by
    dsimp only [z]
    rw [leftInducingHom_val, Langlands.Geometric.stabilizerToInducing_apply]
    exact left_conjugate_radicalElement k r i v
  change leftProjection z = _
  have he : z = ⟨(radicalElement (leftRadicalColumn k r i v)).val,
      radicalElement_mem_leftSubgroup _⟩ := Subtype.ext hz
  rw [he, leftProjection_radicalElement]

/-- The left radical intersection is the full radical at both representatives. -/
theorem leftRadicalIntersection_eq_top (i : Fin 2) :
    leftRadicalIntersection k r R i = ⊤ := by
  apply top_unique
  intro v _
  rw [← radicalElement_coordinates v]
  exact radicalElement_mem_leftRadicalIntersection k r i _

/-- At the cycle representative the coefficient retains coordinates
`k, ..., k+r` of the ambient translation column. -/
theorem leftRadicalCoefficient_zero (v : Fin (k + r + 2) → R) :
    leftRadicalCoefficient k r R 0 (leftOrbitRadicalElement k r 0 v) =
      (1, (radicalElement (fun j : Fin (r + 1) => v ⟨k + j.val, by omega⟩)).val) := by
  rw [leftRadicalCoefficient_element]
  have hc : (fun j : Fin (r + 1) =>
      leftRadicalColumn k r 0 v ⟨k + 1 + j.val, by omega⟩) =
      (fun j : Fin (r + 1) => v ⟨k + j.val, by omega⟩) := by
    funext j
    dsimp only [leftRadicalColumn]
    simp only [↓reduceIte]
    congr 1
    apply Fin.ext
    change (if k + 1 + j.val = k then k + r + 1
      else if k < k + 1 + j.val then k + 1 + j.val - 1
      else k + 1 + j.val) = k + j.val
    split_ifs <;> omega
  rw [hc]

/-- At the identity representative the coefficient retains coordinates
`k+1, ..., k+r+1` of the ambient translation column. -/
theorem leftRadicalCoefficient_one (v : Fin (k + r + 2) → R) :
    leftRadicalCoefficient k r R 1 (leftOrbitRadicalElement k r 1 v) =
      (1, (radicalElement (fun j : Fin (r + 1) =>
        v ⟨k + 1 + j.val, by omega⟩)).val) := by
  rw [leftRadicalCoefficient_element]
  rfl

/-- The translation column supported only at the final radical coordinate. -/
def terminalRadicalColumn (t : ℕ) (c : R) (j : Fin (t + 1)) : R :=
  if j = Fin.last t then c else 0

@[simp] theorem terminalRadicalColumn_last (t : ℕ) (c : R) :
    terminalRadicalColumn t c (Fin.last t) = c := by
  simp only [terminalRadicalColumn, ↓reduceIte]

/-- The cycle sends this terminal translation to the off-diagonal rectangle,
so its entire left coefficient is the identity. -/
theorem leftRadicalCoefficient_terminal (c : R) :
    leftRadicalCoefficient k r R 0
        (leftOrbitRadicalElement k r 0 (terminalRadicalColumn (k + r + 1) c)) = 1 := by
  rw [leftRadicalCoefficient_zero]
  have hz : (fun j : Fin (r + 1) =>
      terminalRadicalColumn (k + r + 1) c ⟨k + j.val, by omega⟩) = 0 := by
    funext j
    have hj := j.isLt
    simp only [terminalRadicalColumn, Fin.ext_iff, Fin.val_last, Pi.zero_apply]
    split_ifs <;> first | rfl | omega
  rw [hz, radicalElement_zero]
  rfl

end LeftOrbit

section RightOrbit

variable (k r : ℕ) {R : Type u} [CommRing R]

/-- The translation column in the original right mixed coordinates after
inverse conjugation by representative `i` and rank transport. -/
def rightRadicalColumn (i : Fin 2) (v : Fin (k + r + 2) → R)
    (j : Fin (k + 1 + (r + 1))) : R :=
  if i = 0 then
    v (cycleRadicalIndex (k + r + 1) r (Fin.cast (totalRank_eq k r) j))
  else v (Fin.cast (totalRank_eq k r) j)

/-- Inverse conjugation and rank transport at either actual right representative. -/
theorem right_conjugate_radicalElement (i : Fin 2) (v : Fin (k + r + 2) → R) :
    (rankCast (totalRank_eq k r)).symm
        ((rightRepresentative k r R i)⁻¹ * (radicalElement v).val *
          rightRepresentative k r R i) =
      (radicalElement (rightRadicalColumn k r i v)).val := by
  fin_cases i
  · change (rankCast (totalRank_eq k r)).symm
      ((rightRepresentative k r R 0)⁻¹ * (radicalElement v).val *
        rightRepresentative k r R 0) =
      (radicalElement (rightRadicalColumn k r 0 v)).val
    rw [rightRepresentative_zero]
    change (rankCast (totalRank_eq k r)).symm
      ((cycleElement (k + r + 1) r (by omega) R)⁻¹ * (radicalElement v).val *
        cycleElement (k + r + 1) r (by omega) R) = _
    rw [cycleElement_inv_conjugate_radicalElement, rankCast_symm_radicalElement]
    rfl
  · change (rankCast (totalRank_eq k r)).symm
      ((rightRepresentative k r R 1)⁻¹ * (radicalElement v).val *
        rightRepresentative k r R 1) =
      (radicalElement (rightRadicalColumn k r 1 v)).val
    simp only [rightRepresentative_one, inv_one, one_mul, mul_one,
      rankCast_symm_radicalElement]
    rfl

/-- The exact right radical-intersection condition in the transported coordinates. -/
theorem radicalElement_mem_rightRadicalIntersection_iff (i : Fin 2)
    (v : Fin (k + r + 2) → R) :
    radicalElement v ∈ rightRadicalIntersection k r R i ↔
      ∀ j : Fin (k + 1),
        rightRadicalColumn k r i v ⟨r + 1 + j.val, by omega⟩ = 0 := by
  rw [mem_radicalIntersection_iff, mem_rightInducing_iff,
    right_conjugate_radicalElement, radicalElement_mem_rightSubgroup_iff]

/-- A translation satisfying the actual right intersection condition. -/
def rightOrbitRadicalElement (i : Fin 2) (v : Fin (k + r + 2) → R)
    (hv : radicalElement v ∈ rightRadicalIntersection k r R i) :
    rightRadicalIntersection k r R i :=
  ⟨radicalElement v, hv⟩

/-- The exact coefficient of a translation at either actual right representative. -/
theorem rightRadicalCoefficient_element (i : Fin 2) (v : Fin (k + r + 2) → R)
    (hv : radicalElement v ∈ rightRadicalIntersection k r R i) :
    rightRadicalCoefficient k r R i (rightOrbitRadicalElement k r i v hv) =
      ((radicalElement (fun j : Fin (r + 1) =>
        rightRadicalColumn k r i v ⟨j.val, by omega⟩)).val, 1) := by
  let z := (rightInducingHom k r R)
    (Langlands.Geometric.stabilizerToInducing (rightInducing k r R)
      (plusSubgroup (k + r + 1) R) (rightRepresentative k r R i)
      (rightRadicalInclusion k r R i (rightOrbitRadicalElement k r i v hv)))
  have hz : z.val = (radicalElement (rightRadicalColumn k r i v)).val := by
    dsimp only [z]
    rw [rightInducingHom_val, Langlands.Geometric.stabilizerToInducing_apply]
    exact right_conjugate_radicalElement k r i v
  change rightProjection z = _
  have he : z = ⟨(radicalElement (rightRadicalColumn k r i v)).val,
      by rw [← hz]; exact z.property⟩ := Subtype.ext hz
  rw [he, rightProjection_radicalElement]

omit [CommRing R] in
private theorem rightRadicalColumn_zero_middle
    (v : Fin (k + r + 2) → R) (j : Fin (k + 1)) :
    rightRadicalColumn k r 0 v ⟨r + 1 + j.val, by omega⟩ =
      v ⟨r + j.val, by omega⟩ := by
  dsimp only [rightRadicalColumn]
  simp only [↓reduceIte]
  congr 1
  apply Fin.ext
  change (if r + 1 + j.val = r then k + r + 1
    else if r < r + 1 + j.val then r + 1 + j.val - 1
    else r + 1 + j.val) = r + j.val
  split_ifs <;> omega

/-- At the right cycle, precisely coordinates `r, ..., r+k` must vanish. -/
theorem radicalElement_mem_rightRadicalIntersection_zero_iff
    (v : Fin (k + r + 2) → R) :
    radicalElement v ∈ rightRadicalIntersection k r R 0 ↔
      ∀ j : Fin (k + 1), v ⟨r + j.val, by omega⟩ = 0 := by
  rw [radicalElement_mem_rightRadicalIntersection_iff]
  simp only [rightRadicalColumn_zero_middle]

/-- At the right identity, precisely coordinates `r+1, ..., r+k+1` must vanish. -/
theorem radicalElement_mem_rightRadicalIntersection_one_iff
    (v : Fin (k + r + 2) → R) :
    radicalElement v ∈ rightRadicalIntersection k r R 1 ↔
      ∀ j : Fin (k + 1), v ⟨r + 1 + j.val, by omega⟩ = 0 := by
  rw [radicalElement_mem_rightRadicalIntersection_iff]
  rfl

/-- The right cycle coefficient retains the initial `r` coordinates and uses
the ambient terminal coordinate as its own final radical coordinate. -/
theorem rightRadicalCoefficient_zero (v : Fin (k + r + 2) → R)
    (hv : radicalElement v ∈ rightRadicalIntersection k r R 0) :
    rightRadicalCoefficient k r R 0 (rightOrbitRadicalElement k r 0 v hv) =
      ((radicalElement (fun j : Fin (r + 1) =>
        if j.val = r then v (Fin.last (k + r + 1))
        else v ⟨j.val, by omega⟩)).val, 1) := by
  rw [rightRadicalCoefficient_element]
  have hc : (fun j : Fin (r + 1) =>
      rightRadicalColumn k r 0 v ⟨j.val, by omega⟩) =
      (fun j : Fin (r + 1) => if j.val = r then v (Fin.last (k + r + 1))
        else v ⟨j.val, by omega⟩) := by
    funext j
    dsimp only [rightRadicalColumn]
    simp only [↓reduceIte]
    by_cases hj : j.val = r
    · rw [ite_eq_left hj]
      congr 1
      apply Fin.ext
      change (if j.val = r then k + r + 1
        else if r < j.val then j.val - 1 else j.val) = k + r + 1
      rw [ite_eq_left hj]
    · rw [ite_eq_right hj]
      congr 1
      apply Fin.ext
      change (if j.val = r then k + r + 1
        else if r < j.val then j.val - 1 else j.val) = j.val
      have := j.isLt
      split_ifs <;> omega
  rw [hc]

/-- The right identity coefficient retains the first `r+1` translation coordinates. -/
theorem rightRadicalCoefficient_one (v : Fin (k + r + 2) → R)
    (hv : radicalElement v ∈ rightRadicalIntersection k r R 1) :
    rightRadicalCoefficient k r R 1 (rightOrbitRadicalElement k r 1 v hv) =
      ((radicalElement (fun j : Fin (r + 1) => v ⟨j.val, by omega⟩)).val, 1) := by
  rw [rightRadicalCoefficient_element]
  rfl

/-- The ambient terminal coordinate vanishes in the right identity intersection. -/
theorem rightRadicalIntersection_one_terminal_zero (v : Fin (k + r + 2) → R)
    (hv : radicalElement v ∈ rightRadicalIntersection k r R 1) :
    v (Fin.last (k + r + 1)) = 0 := by
  have h := (radicalElement_mem_rightRadicalIntersection_one_iff k r v).mp hv
    (Fin.last k)
  have hi : (⟨r + 1 + (Fin.last k).val, by omega⟩ : Fin (k + r + 2)) =
      Fin.last (k + r + 1) := by
    apply Fin.ext
    simp only [Fin.val_last]
    omega
  simpa only [hi] using h

end RightOrbit

end Langlands.GeneralLinear.Mirabolic.MixedOrbit
