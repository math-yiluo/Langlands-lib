import Langlands.Group.GL.UpperUnipotent
import Langlands.Group.GL.Maps
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Unipotent orbits on a Grassmannian by row echelon forms

For a field `K`, a matrix `g` of size `n` and `a ≤ n`, the span of the rows of `g` with index at
least `a` is a subspace of `Kⁿ` of row vectors. Two invertible matrices have the same such span
exactly when they differ by a left factor whose lower left block (rows `≥ a`, columns `< a`)
vanishes. The upper unitriangular group acts on these spans by right multiplication, preserving
the set of leading positions (pivots). Every span is the image of a coordinate span under an upper
unitriangular matrix (row echelon form). See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

open Matrix Module

namespace Langlands.Global.CuspidalPairEisenstein.RowEchelon

variable {K : Type*} [Field K] {n : ℕ}

/-- The span of the rows of `g` whose index is at least `a`. -/
def lowerRowSpace (a : ℕ) (g : Matrix (Fin n) (Fin n) K) : Submodule K (Fin n → K) :=
  Submodule.span K ((fun i => g i) '' {i | a ≤ (i : ℕ)})

/-- The coordinate subspace of vectors supported on `J`. -/
def coordSpace (J : Finset (Fin n)) : Submodule K (Fin n → K) where
  carrier := {v | ∀ i, i ∉ J → v i = 0}
  add_mem' hv hw i hi := by simp [hv i hi, hw i hi]
  zero_mem' i _ := rfl
  smul_mem' c v hv i hi := by simp [hv i hi]

theorem mem_coordSpace {J : Finset (Fin n)} {v : Fin n → K} :
    v ∈ coordSpace J ↔ ∀ i, i ∉ J → v i = 0 := Iff.rfl

/-- The vanishing of the lower left block, for rows `≥ a` and columns `< a`. -/
def LowerLeftZero (a : ℕ) (g : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ i j : Fin n, a ≤ (i : ℕ) → (j : ℕ) < a → g i j = 0

theorem row_mul (g h : Matrix (Fin n) (Fin n) K) (i : Fin n) : (g * h) i = g i ᵥ* h := by
  ext j
  rfl

theorem row_eq_sum (g h : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    (g * h) i = ∑ k, g i k • h k := by
  ext j
  simp [Matrix.mul_apply, Finset.sum_apply]

theorem lowerRowSpace_mul_right (a : ℕ) (g h : Matrix (Fin n) (Fin n) K) :
    lowerRowSpace a (g * h) = (lowerRowSpace a g).map (vecMulLinear h) := by
  rw [lowerRowSpace, lowerRowSpace, Submodule.map_span, Set.image_image]
  rfl

theorem lowerRowSpace_mul_left_le (a : ℕ) {p : Matrix (Fin n) (Fin n) K}
    (hp : LowerLeftZero a p) (g : Matrix (Fin n) (Fin n) K) :
    lowerRowSpace a (p * g) ≤ lowerRowSpace a g := by
  rw [lowerRowSpace, Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  change (p * g) i ∈ lowerRowSpace a g
  rw [row_eq_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : a ≤ (k : ℕ)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
  · rw [hp i k hi (by omega), zero_smul]
    exact Submodule.zero_mem _

/-- The rows `≥ a` of the identity span vectors vanishing below `a`. -/
theorem lowerRowSpace_one_le (a : ℕ) (v : Fin n → K)
    (hv : v ∈ lowerRowSpace a (1 : Matrix (Fin n) (Fin n) K)) (j : Fin n) (hj : (j : ℕ) < a) :
    v j = 0 := by
  let S : Submodule K (Fin n → K) :=
    { carrier := {w | ∀ j : Fin n, (j : ℕ) < a → w j = 0}
      add_mem' := fun hv hw j hj => by simp [hv j hj, hw j hj]
      zero_mem' := fun _ _ => rfl
      smul_mem' := fun c v hv j hj => by simp [hv j hj] }
  have hle : lowerRowSpace a (1 : Matrix (Fin n) (Fin n) K) ≤ S := by
    rw [lowerRowSpace, Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩ j' hj'
    have hi' : a ≤ (i : ℕ) := hi
    change (1 : Matrix (Fin n) (Fin n) K) i j' = 0
    have hne : i ≠ j' := Fin.ne_of_val_ne (by omega)
    rw [Matrix.one_apply_ne hne]
  exact hle hv j hj

/-- If the rows `≥ a` of `g'` lie in the span of the rows `≥ a` of the invertible `g`, then
`g' g⁻¹` has vanishing lower left block. -/
theorem lowerLeftZero_mul_inv_of_le (a : ℕ) (g g' : Matrix.GeneralLinearGroup (Fin n) K)
    (h : lowerRowSpace a (g' : Matrix (Fin n) (Fin n) K) ≤
      lowerRowSpace a (g : Matrix (Fin n) (Fin n) K)) :
    LowerLeftZero a ((g' * g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) := by
  intro i j hi hj
  have hmem : (g' : Matrix (Fin n) (Fin n) K) i ∈ lowerRowSpace a (g : Matrix (Fin n) (Fin n) K) :=
    h (Submodule.subset_span ⟨i, hi, rfl⟩)
  have hmap : (vecMulLinear ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) ((g' : Matrix (Fin n) (Fin n) K) i) ∈
      lowerRowSpace a (1 : Matrix (Fin n) (Fin n) K) := by
    have h1 : ((g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [← h1, lowerRowSpace_mul_right]
    exact Submodule.mem_map_of_mem hmem
  have := lowerRowSpace_one_le a _ hmap j hj
  rw [Units.val_mul, row_mul] at *
  simpa using this


/-! ### Coordinate spaces -/

theorem single_mem_coordSpace {J : Finset (Fin n)} {j : Fin n} (hj : j ∈ J) :
    (Pi.single j 1 : Fin n → K) ∈ coordSpace J := by
  intro i hi
  rw [Pi.single_apply, ite_eq_right]
  rintro rfl
  exact hi hj

theorem span_single_eq_coordSpace (J : Finset (Fin n)) :
    Submodule.span K ((fun j => (Pi.single j 1 : Fin n → K)) '' (J : Set (Fin n))) =
      coordSpace J := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    exact single_mem_coordSpace hj
  · intro v hv
    have hv' : v = ∑ j ∈ J, v j • (Pi.single j 1 : Fin n → K) := by
      ext i
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq]
      split_ifs with hi
      · rfl
      · exact hv i hi
    rw [hv']
    exact Submodule.sum_mem _ fun j hj =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)

/-- Coordinate spaces have the dimension of their support. -/
def coordSpaceEquiv (J : Finset (Fin n)) : coordSpace (K := K) J ≃ₗ[K] (J → K) where
  toFun v j := (v : Fin n → K) j
  invFun f := ⟨fun i => if h : i ∈ J then f ⟨i, h⟩ else 0, fun i hi => by simp [hi]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := by
    apply Subtype.ext
    ext i
    by_cases hi : i ∈ J
    · simp [hi]
    · simp [hi, v.2 i hi]
  right_inv f := by
    ext j
    simp [j.2]

theorem finrank_coordSpace (J : Finset (Fin n)) : finrank K (coordSpace (K := K) J) = J.card := by
  rw [(coordSpaceEquiv J).finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

theorem finrank_map_vecMulLinear (W : Submodule K (Fin n → K))
    (g : Matrix.GeneralLinearGroup (Fin n) K) :
    finrank K (W.map (vecMulLinear (g : Matrix (Fin n) (Fin n) K))) = finrank K W := by
  have hinj : Function.Injective (vecMulLinear (g : Matrix (Fin n) (Fin n) K)) := by
    intro v w h
    have := congrArg (fun x => x ᵥ* ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) h
    simpa [vecMul_vecMul, ← Units.val_mul] using this
  exact (Submodule.equivMapOfInjective _ hinj W).finrank_eq.symm

theorem map_vecMulLinear_mul (W : Submodule K (Fin n → K)) (g h : Matrix (Fin n) (Fin n) K) :
    W.map (vecMulLinear (g * h)) = (W.map (vecMulLinear g)).map (vecMulLinear h) := by
  rw [← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro v
  simp [vecMul_vecMul]

theorem map_vecMulLinear_one (W : Submodule K (Fin n → K)) :
    W.map (vecMulLinear (1 : Matrix (Fin n) (Fin n) K)) = W := by
  ext v
  simp

theorem map_map_inv (W : Submodule K (Fin n → K)) (g : Matrix.GeneralLinearGroup (Fin n) K) :
    (W.map (vecMulLinear (g : Matrix (Fin n) (Fin n) K))).map
      (vecMulLinear ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      W := by
  rw [← map_vecMulLinear_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    map_vecMulLinear_one]

theorem map_inv_map (W : Submodule K (Fin n → K)) (g : Matrix.GeneralLinearGroup (Fin n) K) :
    (W.map (vecMulLinear ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K))).map (vecMulLinear (g : Matrix (Fin n) (Fin n) K)) = W := by
  rw [← map_vecMulLinear_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    map_vecMulLinear_one]

theorem lowerRowSpace_one (a : ℕ) :
    lowerRowSpace a (1 : Matrix (Fin n) (Fin n) K) =
      coordSpace (Finset.univ.filter fun i : Fin n => a ≤ (i : ℕ)) := by
  rw [← span_single_eq_coordSpace, lowerRowSpace]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]
  constructor <;> rintro ⟨i, hi, rfl⟩ <;> exact ⟨i, hi, by ext j; simp [Matrix.one_apply,
    Pi.single_apply, eq_comm]⟩

theorem finrank_lowerRowSpace (a : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) K) :
    finrank K (lowerRowSpace a (g : Matrix (Fin n) (Fin n) K)) = n - a := by
  have h : (g : Matrix (Fin n) (Fin n) K) = 1 * g := (one_mul _).symm
  rw [h, lowerRowSpace_mul_right, finrank_map_vecMulLinear, lowerRowSpace_one,
    finrank_coordSpace]
  have : (Finset.univ.filter fun i : Fin n => a ≤ (i : ℕ)) =
      (Finset.univ.filter fun i : Fin n => (i : ℕ) < a)ᶜ := by
    ext i
    simp
  rw [this, Finset.card_compl, Fintype.card_fin, Fin.card_filter_val_lt, Nat.min_def]
  split_ifs <;> omega

/-- A matrix maps a coordinate space into itself exactly when its entries from `J` to the
complement of `J` vanish. -/
theorem coordSpace_map_le_iff (J : Finset (Fin n)) (g : Matrix (Fin n) (Fin n) K) :
    (coordSpace J).map (vecMulLinear g) ≤ coordSpace J ↔ ∀ i ∈ J, ∀ j, j ∉ J → g i j = 0 := by
  constructor
  · intro h i hi j hj
    have hmem := h (Submodule.mem_map_of_mem (f := vecMulLinear g) (single_mem_coordSpace hi))
    have := hmem j hj
    simpa [single_one_vecMul] using this
  · rintro h _ ⟨v, hv, rfl⟩ j hj
    simp only [vecMulLinear_apply, vecMul, dotProduct]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ∈ J
    · rw [h k hk j hj, mul_zero]
    · rw [hv k hk, zero_mul]

/-! ### Pivots -/

/-- `j` is the leading position of `v`: its first nonzero coordinate. -/
def IsLead (v : Fin n → K) (j : Fin n) : Prop :=
  v j ≠ 0 ∧ ∀ i, i < j → v i = 0

theorem exists_isLead {v : Fin n → K} (hv : v ≠ 0) : ∃ j, IsLead v j := by
  classical
  have hs : (Finset.univ.filter fun i => v i ≠ 0).Nonempty := by
    by_contra h
    apply hv
    ext i
    by_contra hi
    exact h ⟨i, by simpa using hi⟩
  refine ⟨(Finset.univ.filter fun i => v i ≠ 0).min' hs, ?_, fun i hi => ?_⟩
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ hs)).2
  · by_contra h
    exact absurd (Finset.min'_le _ i (by simp [h])) (not_le.mpr hi)

theorem IsLead.eq {v : Fin n → K} {j k : Fin n} (hj : IsLead v j) (hk : IsLead v k) : j = k := by
  rcases lt_trichotomy j k with h | h | h
  · exact absurd (hk.2 j h) hj.1
  · exact h
  · exact absurd (hj.2 k h) hk.1

theorem IsLead.vecMul {v : Fin n → K} {j : Fin n} (hv : IsLead v j)
    {u : Matrix (Fin n) (Fin n) K} (hu : u.IsUpperTriangular) (hd : ∀ i, u i i = 1) :
    IsLead (v ᵥ* u) j := by
  have hlow : ∀ i, i < j → (v ᵥ* u) i = 0 := by
    intro i hi
    simp only [Matrix.vecMul, dotProduct]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k < j
    · rw [hv.2 k hk, zero_mul]
    · rw [hu (lt_of_lt_of_le hi (not_lt.mp hk)), mul_zero]
  refine ⟨?_, hlow⟩
  have : (v ᵥ* u) j = v j := by
    simp only [Matrix.vecMul, dotProduct]
    rw [Finset.sum_eq_single j]
    · rw [hd j, mul_one]
    · intro k _ hkj
      rcases lt_or_gt_of_ne hkj with hk | hk
      · rw [hv.2 k hk, zero_mul]
      · rw [hu hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [this]
  exact hv.1

open Classical in
/-- The pivots of `W`: the leading positions of its nonzero vectors. -/
def pivots (W : Submodule K (Fin n → K)) : Finset (Fin n) :=
  Finset.univ.filter fun j => ∃ v ∈ W, IsLead v j

theorem mem_pivots {W : Submodule K (Fin n → K)} {j : Fin n} :
    j ∈ pivots W ↔ ∃ v ∈ W, IsLead v j := by
  unfold pivots
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem pivots_map_unipotent (W : Submodule K (Fin n → K))
    {u : Matrix.GeneralLinearGroup (Fin n) K} (hu : u ∈ GeneralLinear.upperUnipotent n K) :
    pivots (W.map (vecMulLinear (u : Matrix (Fin n) (Fin n) K))) = pivots W := by
  have hu' : u⁻¹ ∈ GeneralLinear.upperUnipotent n K :=
    (GeneralLinear.upperUnipotent n K).inv_mem hu
  ext j
  rw [mem_pivots, mem_pivots]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, hlead⟩
    refine ⟨v, hv, ?_⟩
    have h := hlead.vecMul hu'.1 hu'.2
    simpa [vecMul_vecMul, ← Units.val_mul] using h
  · rintro ⟨v, hv, hlead⟩
    exact ⟨_, Submodule.mem_map_of_mem hv, hlead.vecMul hu.1 hu.2⟩

theorem pivots_coordSpace (J : Finset (Fin n)) : pivots (coordSpace (K := K) J) = J := by
  ext j
  rw [mem_pivots]
  constructor
  · rintro ⟨v, hv, hlead⟩
    by_contra hj
    exact hlead.1 (hv j hj)
  · intro hj
    refine ⟨Pi.single j 1, single_mem_coordSpace hj, by simp, fun i hi => ?_⟩
    rw [Pi.single_apply, ite_eq_right (ne_of_lt hi)]

/-- Restriction of a subspace to its pivot coordinates. -/
def pivotRestrict (W : Submodule K (Fin n → K)) : W →ₗ[K] (pivots W → K) where
  toFun w j := (w : Fin n → K) j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pivotRestrict_injective (W : Submodule K (Fin n → K)) :
    Function.Injective (pivotRestrict W) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  by_contra hne
  have hne' : (w : Fin n → K) ≠ 0 := fun h => hne (Subtype.ext h)
  obtain ⟨j, hj⟩ := exists_isLead hne'
  have hjp : j ∈ pivots W := mem_pivots.mpr ⟨w, w.2, hj⟩
  exact hj.1 (congrFun hw ⟨j, hjp⟩)

theorem card_pivots (W : Submodule K (Fin n → K)) : (pivots W).card = finrank K W := by
  apply le_antisymm
  · -- vectors with distinct leading positions are linearly independent
    have hchoose : ∀ j : pivots W, ∃ v ∈ W, IsLead v j := fun j => mem_pivots.mp j.2
    choose v hvW hvl using hchoose
    let b : pivots W → W := fun j => ⟨v j, hvW j⟩
    have hb : LinearIndependent K b := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      by_contra hne
      push Not at hne
      classical
      let S : Finset (pivots W) := Finset.univ.filter fun i => c i ≠ 0
      have hS : S.Nonempty := by
        obtain ⟨i, hi⟩ := hne
        exact ⟨i, by simp [S, hi]⟩
      let i₀ := S.min' hS
      have hi₀ : c i₀ ≠ 0 := (Finset.mem_filter.mp (S.min'_mem hS)).2
      have hsum := congrArg (fun w : W => (w : Fin n → K) (i₀ : Fin n)) hc
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Submodule.coe_zero, Pi.zero_apply, b] at hsum
      rw [Finset.sum_eq_single i₀] at hsum
      · exact mul_ne_zero hi₀ (hvl i₀).1 hsum
      · intro i _ hii₀
        by_cases hci : c i = 0
        · rw [hci, zero_mul]
        · have hle : i₀ ≤ i := S.min'_le i (by simp [S, hci])
          have hlt : (i₀ : Fin n) < i := lt_of_le_of_ne hle (fun h => hii₀ (Subtype.ext h).symm)
          rw [(hvl i).2 _ hlt, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i₀) h
    have := hb.fintype_card_le_finrank
    simpa using this
  · have := LinearMap.finrank_le_finrank_of_injective (pivotRestrict_injective W)
    simpa [Module.finrank_fintype_fun_eq_card] using this

/-- **Row echelon form.** Every subspace is the image of the coordinate space on its pivots under
an upper unitriangular matrix. -/
theorem exists_unipotent_map_coordSpace (W : Submodule K (Fin n → K)) :
    ∃ u ∈ GeneralLinear.upperUnipotent n K,
      W = (coordSpace (pivots W)).map (vecMulLinear (u : Matrix (Fin n) (Fin n) K)) := by
  classical
  set J := pivots W with hJ
  have hsurj : Function.Surjective (pivotRestrict W) := by
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact pivotRestrict_injective W
    · rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, card_pivots]
  choose w hw using fun j : J => hsurj (Pi.single j 1)
  have hwJ : ∀ (j : J) (k : J), (w j : Fin n → K) k = if k = j then 1 else 0 := by
    intro j k
    have := congrFun (hw j) k
    simpa [pivotRestrict, Pi.single_apply] using this
  have hlead : ∀ j : J, IsLead (w j : Fin n → K) j := by
    intro j
    have hne : (w j : Fin n → K) ≠ 0 := by
      intro h
      have := hwJ j j
      rw [h, ite_eq_left rfl] at this
      exact zero_ne_one this
    obtain ⟨l, hl⟩ := exists_isLead hne
    have hlJ : l ∈ J := mem_pivots.mpr ⟨w j, (w j).2, hl⟩
    have hlj : l = j := by
      by_contra hne'
      have := hwJ j ⟨l, hlJ⟩
      rw [ite_eq_right (fun h => hne' (congrArg Subtype.val h))] at this
      exact hl.1 this
    rw [← hlj]
    exact hl
  let U : Matrix (Fin n) (Fin n) K := fun i =>
    if h : i ∈ J then (w ⟨i, h⟩ : Fin n → K) else Pi.single i 1
  have hUtri : U.IsUpperTriangular := by
    intro i j hji
    simp only [U]
    split_ifs with hi
    · exact (hlead ⟨i, hi⟩).2 j hji
    · rw [Pi.single_apply, ite_eq_right (ne_of_lt (show j < i from hji))]
  have hUdiag : ∀ i, U i i = 1 := by
    intro i
    simp only [U]
    split_ifs with hi
    · simpa using hwJ ⟨i, hi⟩ ⟨i, hi⟩
    · simp
  have hdet : IsUnit U.det := by
    rw [Matrix.det_of_isUpperTriangular hUtri, Finset.prod_eq_one fun i _ => hUdiag i]
    exact isUnit_one
  let u : Matrix.GeneralLinearGroup (Fin n) K := Matrix.nonsingInvUnit U hdet
  have hu : u ∈ GeneralLinear.upperUnipotent n K := ⟨hUtri, hUdiag⟩
  refine ⟨u, hu, ?_⟩
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨v, hv, rfl⟩
    change v ᵥ* U ∈ W
    rw [vecMul_eq_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : k ∈ J
    · have : U k = (w ⟨k, hk⟩ : Fin n → K) := by simp [U, hk]
      rw [this]
      exact Submodule.smul_mem _ _ (w ⟨k, hk⟩).2
    · rw [hv k hk, zero_smul]
      exact Submodule.zero_mem _
  · rw [finrank_map_vecMulLinear, finrank_coordSpace, card_pivots]

/-! ### The pattern subgroups `Λ_J` over a commutative ring -/

section Pattern

variable {R : Type*} [CommRing R]

/-- The pattern subgroup `Λ_J`: upper unitriangular matrices whose entries from `J` to its
complement vanish. Over a field it is the stabilizer of the coordinate space of `J` in the upper
unitriangular group. -/
def stabilizer (J : Finset (Fin n)) : Subgroup (Matrix.GeneralLinearGroup (Fin n) R) where
  carrier := {g | g ∈ GeneralLinear.upperUnipotent n R ∧
    ∀ i ∈ J, ∀ j, j ∉ J → (g : Matrix (Fin n) (Fin n) R) i j = 0}
  one_mem' := ⟨(GeneralLinear.upperUnipotent n R).one_mem, fun i hi j hj => by
    rw [Units.val_one, Matrix.one_apply_ne]
    rintro rfl
    exact hj hi⟩
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨(GeneralLinear.upperUnipotent n R).mul_mem hg hh, fun i hi j hj => ?_⟩
    rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ∈ J
    · rw [hh' k hk j hj, mul_zero]
    · rw [hg' i hi k hk, zero_mul]
  inv_mem' := by
    classical
    rintro g ⟨hg, hg'⟩
    refine ⟨(GeneralLinear.upperUnipotent n R).inv_mem hg, ?_⟩
    let := g.invertible
    let b : Fin n → ℕ := fun i => if i ∈ J then 1 else 0
    have hb : Matrix.BlockTriangular (g : Matrix (Fin n) (Fin n) R) b := by
      intro i j hij
      by_cases hi : i ∈ J
      · by_cases hj : j ∈ J
        · simp [b, hi, hj] at hij
        · exact hg' i hi j hj
      · simp [b, hi] at hij
    have hinv := Matrix.blockTriangular_inv_of_blockTriangular hb
    intro i hi j hj
    rw [Matrix.GeneralLinearGroup.coe_inv]
    exact hinv (by simp [b, hi, hj])

theorem mem_stabilizer {J : Finset (Fin n)} {g : Matrix.GeneralLinearGroup (Fin n) R} :
    g ∈ stabilizer (R := R) J ↔ g ∈ GeneralLinear.upperUnipotent n R ∧
      ∀ i ∈ J, ∀ j, j ∉ J → (g : Matrix (Fin n) (Fin n) R) i j = 0 := Iff.rfl

end Pattern

/-! ### Cosets of the lower-left-zero subgroup -/

variable (a : ℕ) (P : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
  (hP : ∀ g : Matrix.GeneralLinearGroup (Fin n) K,
    g ∈ P ↔ LowerLeftZero a (g : Matrix (Fin n) (Fin n) K))

include hP in
/-- Two invertible matrices lie in the same right coset of `P` exactly when their rows `≥ a`
span the same subspace. -/
theorem rightRel_iff (g g' : Matrix.GeneralLinearGroup (Fin n) K) :
    QuotientGroup.rightRel P g g' ↔
      lowerRowSpace a (g : Matrix (Fin n) (Fin n) K) =
        lowerRowSpace a (g' : Matrix (Fin n) (Fin n) K) := by
  rw [QuotientGroup.rightRel_apply]
  constructor
  · intro h
    have h' : g * g'⁻¹ ∈ P := by simpa using P.inv_mem h
    have e1 : (g' : Matrix (Fin n) (Fin n) K) =
        ((g' * g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * g := by
      rw [← Units.val_mul, inv_mul_cancel_right]
    have e2 : (g : Matrix (Fin n) (Fin n) K) =
        ((g * g'⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * g' := by
      rw [← Units.val_mul, inv_mul_cancel_right]
    apply le_antisymm
    · conv_lhs => rw [e2]
      exact lowerRowSpace_mul_left_le a ((hP _).mp h') _
    · conv_lhs => rw [e1]
      exact lowerRowSpace_mul_left_le a ((hP _).mp h) _
  · intro h
    exact (hP _).mpr (lowerLeftZero_mul_inv_of_le a g g' h.symm.le)

theorem map_coordSpace_eq_iff (J : Finset (Fin n)) (u u' : Matrix.GeneralLinearGroup (Fin n) K)
    (hu : u ∈ GeneralLinear.upperUnipotent n K) (hu' : u' ∈ GeneralLinear.upperUnipotent n K) :
    (coordSpace J).map (vecMulLinear (u : Matrix (Fin n) (Fin n) K)) =
        (coordSpace J).map (vecMulLinear (u' : Matrix (Fin n) (Fin n) K)) ↔
      u' * u⁻¹ ∈ stabilizer (R := K) J := by
  have hmem : u' * u⁻¹ ∈ GeneralLinear.upperUnipotent n K :=
    (GeneralLinear.upperUnipotent n K).mul_mem hu' ((GeneralLinear.upperUnipotent n K).inv_mem hu)
  have key : (coordSpace (K := K) J).map (vecMulLinear (((u' * u⁻¹ :
      Matrix.GeneralLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K)) =
      ((coordSpace J).map (vecMulLinear (u' : Matrix (Fin n) (Fin n) K))).map
        (vecMulLinear ((u⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K)) := by
    rw [Units.val_mul, map_vecMulLinear_mul]
  constructor
  · intro h
    refine ⟨hmem, (coordSpace_map_le_iff J _).mp ?_⟩
    rw [key, ← h, map_map_inv]
  · rintro ⟨_, h⟩
    have hle := (coordSpace_map_le_iff J _).mpr h
    rw [key] at hle
    have hle' := Submodule.map_mono (f := vecMulLinear (u : Matrix (Fin n) (Fin n) K)) hle
    rw [map_inv_map] at hle'
    exact (Submodule.eq_of_le_of_finrank_eq hle'
      (by rw [finrank_map_vecMulLinear, finrank_map_vecMulLinear])).symm

/-! ### The orbit decomposition -/

/-- The possible pivot sets of the spans of the rows `≥ a`: subsets of size `n - a`. -/
abbrev PivotIndex (n a : ℕ) := {J : Finset (Fin n) // J.card = n - a}

/-- Right cosets `Λ_J \ N` of the stabilizer of the coordinate space of `J` in the upper
unitriangular group `N`. -/
abbrev StabilizerCosets (J : Finset (Fin n)) :=
  Quotient (QuotientGroup.rightRel
    ((stabilizer (R := K) J).subgroupOf (GeneralLinear.upperUnipotent n K)))

variable (rep : Finset (Fin n) → Matrix.GeneralLinearGroup (Fin n) K)

/-- The map `(J, Λ_J δ) ↦ P γ_J δ` with chosen coset representatives `δ`. -/
def orbitMap : (Σ J : PivotIndex n a, StabilizerCosets (K := K) J.1) →
    Quotient (QuotientGroup.rightRel P) :=
  fun x => Quotient.mk _ (rep x.1.1 *
    ((Quotient.out x.2 : GeneralLinear.upperUnipotent n K) : Matrix.GeneralLinearGroup (Fin n) K))

variable (hrep : ∀ J : Finset (Fin n), J.card = n - a →
  lowerRowSpace a (rep J : Matrix (Fin n) (Fin n) K) = coordSpace J)

include hP hrep in
/-- **Orbit decomposition.** If `P` consists exactly of the invertible matrices with vanishing
lower left block (`hP`) and the rows `≥ a` of each `γ_J` span the coordinate space of `J`
(`hrep`), then `(J, Λ_J δ) ↦ P γ_J δ` is a bijection from the disjoint union over the subsets
`J` of size `n - a` of `Λ_J \ N` onto `P \ GL_n`. -/
theorem orbitMap_bijective : Function.Bijective (orbitMap a P rep) := by
  constructor
  · rintro ⟨⟨J, hJ⟩, q⟩ ⟨⟨J', hJ'⟩, q'⟩ h
    have h1 : QuotientGroup.rightRel P (rep J * ((Quotient.out q : GeneralLinear.upperUnipotent n K) :
        Matrix.GeneralLinearGroup (Fin n) K)) (rep J' * ((Quotient.out q' :
          GeneralLinear.upperUnipotent n K) : Matrix.GeneralLinearGroup (Fin n) K)) :=
      Quotient.exact h
    rw [rightRel_iff a P hP, Units.val_mul, Units.val_mul, lowerRowSpace_mul_right,
      lowerRowSpace_mul_right, hrep J hJ, hrep J' hJ'] at h1
    have hJJ : J = J' := by
      have := congrArg pivots h1
      rwa [pivots_map_unipotent _ (Quotient.out q).2, pivots_map_unipotent _ (Quotient.out q').2,
        pivots_coordSpace, pivots_coordSpace] at this
    subst hJJ
    have hqq : q = q' := by
      rw [← Quotient.out_eq q, ← Quotient.out_eq q']
      apply Quotient.sound
      change QuotientGroup.rightRel _ _ _
      rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
      exact (map_coordSpace_eq_iff J _ _ (Quotient.out q).2 (Quotient.out q').2).mp h1
    subst hqq
    rfl
  · intro x
    induction x using Quotient.inductionOn with
    | h γ =>
      set W := lowerRowSpace a (γ : Matrix (Fin n) (Fin n) K) with hWdef
      obtain ⟨u, hu, hW⟩ := exists_unipotent_map_coordSpace W
      have hcard : (pivots W).card = n - a := by rw [card_pivots, finrank_lowerRowSpace]
      let J : PivotIndex n a := ⟨pivots W, hcard⟩
      let q : StabilizerCosets (K := K) J.1 := Quotient.mk _ ⟨u, hu⟩
      refine ⟨⟨J, q⟩, ?_⟩
      apply Quotient.sound
      change QuotientGroup.rightRel P _ _
      rw [rightRel_iff a P hP, Units.val_mul, lowerRowSpace_mul_right, hrep _ hcard]
      have hrel := Quotient.mk_out (s := QuotientGroup.rightRel
        ((stabilizer (R := K) J.1).subgroupOf (GeneralLinear.upperUnipotent n K))) ⟨u, hu⟩
      change QuotientGroup.rightRel _ _ _ at hrel
      rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf] at hrel
      have hq : (coordSpace J.1).map (vecMulLinear (((Quotient.out q :
          GeneralLinear.upperUnipotent n K) : Matrix.GeneralLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K)) = (coordSpace J.1).map (vecMulLinear
              (u : Matrix (Fin n) (Fin n) K)) :=
        (map_coordSpace_eq_iff J.1 _ u (Quotient.out q).2 hu).mpr hrel
      rw [hq, ← hW]

end Langlands.Global.CuspidalPairEisenstein.RowEchelon
