import Langlands.Representation.RankinSelberg.AdjacentRankCompactAverage
import Langlands.Representation.RankinSelberg.AdjacentRankLowerParabolic

/-! Compact open orbits of the first `n` rows in `GL_(n+1)`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg

open Matrix HarmonicAnalysis Topology

universe uF

section Algebra

variable {K : Type uF} [Field K] {n : ℕ}

/-- The first `n` rows of an invertible matrix of size `n+1`. -/
def adjacentRankFrame (g : GeneralLinear (n + 1) K) :
    Matrix (Fin n) (Fin (n + 1)) K :=
  g.val.submatrix Fin.castSucc id

@[simp] theorem adjacentRankFrame_apply (g : GeneralLinear (n + 1) K)
    (i : Fin n) (j : Fin (n + 1)) :
    adjacentRankFrame g i j = g.val i.castSucc j := rfl

theorem adjacentRankFrame_mul (g k : GeneralLinear (n + 1) K) :
    adjacentRankFrame (g * k) = adjacentRankFrame g * k.val := by
  ext i j
  rfl

@[simp] theorem adjacentRankFrame_one :
    adjacentRankFrame (1 : GeneralLinear (n + 1) K) =
      rectangularJoin (1 : Matrix (Fin n) (Fin n) K) 0 := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [adjacentRankFrame]
  · simp [adjacentRankFrame, Matrix.one_apply]

theorem adjacentRankFrame_eq (g : GeneralLinear (n + 1) K) :
    adjacentRankFrame g =
      rectangularJoin (1 : Matrix (Fin n) (Fin n) K) 0 * g.val := by
  simpa only [one_mul, adjacentRankFrame_one] using adjacentRankFrame_mul 1 g

/-- Left multiplication of a frame agrees with the literal rectangular orbit. -/
theorem adjacentRankFrame_left (h : GeneralLinear n K) (g : GeneralLinear (n + 1) K) :
    rectangularJoin h.val 0 * g.val = h.val * adjacentRankFrame g := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, adjacentRankFrame]

theorem adjacentRankFrame_mul_join_zero
    (A B : Matrix (Fin n) (Fin n) K) :
    A * rectangularJoin B 0 = rectangularJoin (A * B) 0 := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [Matrix.mul_apply]

/-- Every frame has full row rank. -/
theorem adjacentRankFrame_fullRank (g : GeneralLinear (n + 1) K) :
    AdjacentRankFullRank (adjacentRankFrame g) := by
  rw [adjacentRankFrame_eq, adjacentRankFullRank_mul_iff,
    adjacentRankFullRank_join_zero_iff]
  exact isUnit_one

theorem adjacentRankFrame_image_mul_iff
    (J : Subgroup (GeneralLinear (n + 1) K)) (k : J)
    (M : Matrix (Fin n) (Fin (n + 1)) K) :
    M * k.val.val ∈ adjacentRankFrame '' (J : Set (GeneralLinear (n + 1) K)) ↔
      M ∈ adjacentRankFrame '' (J : Set (GeneralLinear (n + 1) K)) := by
  constructor
  · rintro ⟨j, hj, he⟩
    refine ⟨j * k.val⁻¹, J.mul_mem hj (J.inv_mem k.property), ?_⟩
    rw [adjacentRankFrame_mul, he, Matrix.mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.mul_one]
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j * k.val, J.mul_mem hj k.property, adjacentRankFrame_mul j k.val⟩

end Algebra

section LowerParabolic

variable {K : Type uF} [Field K] {r : ℕ}

/-- Vanishing of the last column above the last row characterizes the actual lower parabolic. -/
theorem adjacentRankLower_mem_iff (g : GeneralLinear (r + 2) K) :
    g ∈ (adjacentRankLowerShape r).oppositeParabolic K ↔
      ∀ i : Fin (r + 1), g i.castSucc (Fin.last (r + 1)) = 0 := by
  constructor
  · intro hg
    exact adjacentRankLower_upperRight_zero ⟨g, hg⟩
  · intro hz
    rw [(adjacentRankLowerShape r).mem_oppositeParabolic_iff]
    intro i j a b hij
    have hi : i = 0 := by fin_cases i <;> fin_cases j <;> simp_all
    have hj : j = 1 := by fin_cases i <;> fin_cases j <;> simp_all
    subst i
    subst j
    change Fin (r + 1) at a
    change Fin 1 at b
    have hb : b = 0 := Subsingleton.elim _ _
    subst b
    have ha : a.castAdd 1 = a.castSucc := by apply Fin.ext; rfl
    have hb₀ : (0 : Fin 1).natAdd (r + 1) = Fin.last (r + 1) := by
      apply Fin.ext
      simp
    simpa only [adjacentRankLowerShape,
      Shahidi.twoBlocks_index_first (Nat.succ_pos r) (Nat.succ_pos 0),
      Shahidi.twoBlocks_index_second (Nat.succ_pos r) (Nat.succ_pos 0), ha, hb₀]
      using hz a

/-- The frame of a lower-parabolic element is its first diagonal block followed by zero. -/
theorem adjacentRankLower_frame
    (q : (adjacentRankLowerShape r).oppositeParabolic K) :
    adjacentRankFrame q.val =
      rectangularJoin (adjacentRankLowerLargeProjection q).val 0 := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simpa using adjacentRankLower_upperRight_zero q i
  · simp

/-- A frame of the form `[h,0]` gives both actual lower membership and its large block. -/
theorem adjacentRankLower_of_frame_eq (g : GeneralLinear (r + 2) K)
    (h : GeneralLinear (r + 1) K)
    (he : adjacentRankFrame g = rectangularJoin h.val 0) :
    ∃ q : (adjacentRankLowerShape r).oppositeParabolic K,
      q.val = g ∧ adjacentRankLowerLargeProjection q = h := by
  have hg : g ∈ (adjacentRankLowerShape r).oppositeParabolic K := by
    apply (adjacentRankLower_mem_iff g).mpr
    intro i
    simpa using congrFun (congrFun he i) (Fin.last (r + 1))
  refine ⟨⟨g, hg⟩, rfl, ?_⟩
  apply Units.ext
  ext i j
  simpa using congrFun (congrFun he i) j.castSucc

/-- A rectangular orbit meets a subgroup frame orbit precisely on the corresponding
lower-parabolic double coset, with the prescribed large diagonal block. -/
theorem adjacentRankFrame_orbit_iff
    (J : Subgroup (GeneralLinear (r + 2) K)) (h : GeneralLinear (r + 1) K)
    (g : GeneralLinear (r + 2) K) :
    rectangularJoin h.val 0 * g.val ∈
        adjacentRankFrame '' (J : Set (GeneralLinear (r + 2) K)) ↔
      ∃ (q : (adjacentRankLowerShape r).oppositeParabolic K) (j : J),
        g = q.val * j.val ∧ adjacentRankLowerLargeProjection q = h⁻¹ := by
  constructor
  · rintro ⟨j, hj, hje⟩
    have hh : h⁻¹.val * h.val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hframe : adjacentRankFrame (g * j⁻¹) = rectangularJoin h⁻¹.val 0 := by
      rw [adjacentRankFrame_mul]
      calc
        adjacentRankFrame g * j⁻¹.val =
            (h⁻¹.val * (h.val * adjacentRankFrame g)) * j⁻¹.val := by
          rw [← Matrix.mul_assoc h⁻¹.val, hh, Matrix.one_mul]
        _ = h⁻¹.val * (adjacentRankFrame j * j⁻¹.val) := by
          rw [← adjacentRankFrame_left, ← hje, Matrix.mul_assoc]
        _ = h⁻¹.val * adjacentRankFrame (1 : GeneralLinear (r + 2) K) := by
          rw [← adjacentRankFrame_mul, mul_inv_cancel]
        _ = rectangularJoin h⁻¹.val 0 := by
          rw [adjacentRankFrame_one, adjacentRankFrame_mul_join_zero, Matrix.mul_one]
    obtain ⟨q, hq, hqa⟩ := adjacentRankLower_of_frame_eq (g * j⁻¹) h⁻¹ hframe
    exact ⟨q, ⟨j, hj⟩, by rw [hq]; simp, hqa⟩
  · rintro ⟨q, j, rfl, hq⟩
    refine ⟨j.val, j.property, ?_⟩
    rw [Units.val_mul, ← Matrix.mul_assoc, adjacentRankLower_rectangular_mul, hq,
      mul_inv_cancel, Units.val_one, ← adjacentRankFrame_one,
      ← adjacentRankFrame_mul, one_mul]

/-- The inner subgroup cut out by the compact frame orbit at the identity. -/
def adjacentRankFrameSlice (J : Subgroup (GeneralLinear (r + 2) K)) :
    Subgroup (GeneralLinear (r + 1) K) :=
  (J.comap ((adjacentRankLowerShape r).oppositeParabolic K).subtype).map
    adjacentRankLowerLargeProjection

theorem mem_adjacentRankFrameSlice_iff
    (J : Subgroup (GeneralLinear (r + 2) K)) (h : GeneralLinear (r + 1) K) :
    h ∈ adjacentRankFrameSlice J ↔ rectangularJoin h.val 0 ∈
      adjacentRankFrame '' (J : Set (GeneralLinear (r + 2) K)) := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.val, hq, adjacentRankLower_frame q⟩
  · rintro ⟨j, hj, he⟩
    obtain ⟨q, hq, hqa⟩ := adjacentRankLower_of_frame_eq j h he
    refine ⟨q, ?_, hqa⟩
    change q.val ∈ J
    rw [hq]
    exact hj

end LowerParabolic

section Topology

variable {K : Type uF} [Field K] [TopologicalSpace K] {n : ℕ}

theorem continuous_adjacentRankFrame :
    Continuous (adjacentRankFrame : GeneralLinear (n + 1) K →
      Matrix (Fin n) (Fin (n + 1)) K) :=
  continuous_pi fun i => continuous_pi fun j =>
    (GeneralLinear.entry i.castSucc j).continuous

variable [IsTopologicalDivisionRing K] [T2Space K]

/-- The image of an identity neighborhood contains a neighborhood of the standard frame. -/
theorem adjacentRankFrame_image_mem_nhds {U : Set (GeneralLinear (n + 1) K)}
    (hU : IsOpen U) (h1 : (1 : GeneralLinear (n + 1) K) ∈ U) :
    adjacentRankFrame '' U ∈ 𝓝 (adjacentRankFrame (1 : GeneralLinear (n + 1) K)) := by
  let f : Matrix (Fin n) (Fin (n + 1)) K →
      Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
    fun M i j => Fin.lastCases ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
      (Fin.last n) j) (fun a => M a j) i
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [f, Fin.lastCases_last]
      exact continuous_const
    · simp only [f, Fin.lastCases_castSucc]
      exact continuous_apply i
  have hO : IsOpen (Units.val '' U) :=
    (isOpenEmbedding_generalLinear_val (n + 1)).isOpenMap U hU
  have hf1 : f (adjacentRankFrame (1 : GeneralLinear (n + 1) K)) ∈ Units.val '' U := by
    refine ⟨1, h1, ?_⟩
    ext i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp [f, adjacentRankFrame]
    all_goals rfl
  filter_upwards [hf.continuousAt.preimage_mem_nhds (hO.mem_nhds hf1)] with M hM
  obtain ⟨g, hg, hgf⟩ := hM
  refine ⟨g, hg, ?_⟩
  ext i j
  change g.val i.castSucc j = M i j
  rw [hgf]
  simp [f]

/-- The frame image of an open subgroup is open in the entire rectangular space. -/
theorem isOpen_adjacentRankFrame_image
    (J : Subgroup (GeneralLinear (n + 1) K))
    (hJ : IsOpen (J : Set (GeneralLinear (n + 1) K))) :
    IsOpen (adjacentRankFrame '' (J : Set (GeneralLinear (n + 1) K))) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨j₀, hj₀, rfl⟩
  let φ : Matrix (Fin n) (Fin (n + 1)) K →
      Matrix (Fin n) (Fin (n + 1)) K := fun M => M * (j₀⁻¹).val
  have hφ : Continuous φ := continuous_id.matrix_mul continuous_const
  have hφj : φ (adjacentRankFrame j₀) =
      adjacentRankFrame (1 : GeneralLinear (n + 1) K) := by
    rw [show φ (adjacentRankFrame j₀) = adjacentRankFrame (j₀ * j₀⁻¹) from
      (adjacentRankFrame_mul j₀ j₀⁻¹).symm, mul_inv_cancel]
  have hmem := adjacentRankFrame_image_mem_nhds hJ J.one_mem
  rw [← hφj] at hmem
  filter_upwards [hφ.continuousAt.preimage_mem_nhds hmem] with M hM
  obtain ⟨j₁, hj₁, hj₁M⟩ := hM
  refine ⟨j₁ * j₀, J.mul_mem hj₁ hj₀, ?_⟩
  rw [adjacentRankFrame_mul, hj₁M]
  simp only [φ]
  rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

/-- Compact open frame-orbit indicators are admissible full-rank compact tests. -/
def adjacentRankFrameOrbitTest (J : OpenSubgroup (GeneralLinear (n + 1) K))
    (hJ : IsCompact (J : Set (GeneralLinear (n + 1) K))) :
    adjacentRankCompactTests n K := by
  let S := adjacentRankFrame '' (J : Set (GeneralLinear (n + 1) K))
  have hc : IsCompact S := hJ.image continuous_adjacentRankFrame
  have ho : IsOpen S := isOpen_adjacentRankFrame_image J.toSubgroup J.isOpen
  refine ⟨compactOpenIndicator S hc ho, ?_⟩
  intro M hM
  have hs : tsupport (compactOpenIndicator S hc ho : _ → ℂ) ⊆ S :=
    closure_minimal (by
      intro M hM
      by_contra h
      apply hM
      change S.indicator (fun _ => (1 : ℂ)) M = 0
      exact Set.indicator_of_notMem h _) hc.isClosed
  obtain ⟨g, -, rfl⟩ := hs hM
  exact adjacentRankFrame_fullRank g

@[simp] theorem adjacentRankFrameOrbitTest_apply
    (J : OpenSubgroup (GeneralLinear (n + 1) K))
    (hJ : IsCompact (J : Set (GeneralLinear (n + 1) K)))
    (M : Matrix (Fin n) (Fin (n + 1)) K) :
    (adjacentRankFrameOrbitTest J hJ).val M =
      (adjacentRankFrame '' (J : Set (GeneralLinear (n + 1) K))).indicator
        (fun _ => (1 : ℂ)) M := rfl

theorem adjacentRankFrameOrbitTest_right
    (J : OpenSubgroup (GeneralLinear (n + 1) K))
    (hJ : IsCompact (J : Set (GeneralLinear (n + 1) K))) (k : J)
    (M : Matrix (Fin n) (Fin (n + 1)) K) :
    (adjacentRankFrameOrbitTest J hJ).val (M * k.val.val) =
      (adjacentRankFrameOrbitTest J hJ).val M := by
  classical
  simp only [adjacentRankFrameOrbitTest_apply]
  change (adjacentRankFrame '' (J.toSubgroup : Set _)).indicator (fun _ => (1 : ℂ))
      (M * k.val.val) =
    (adjacentRankFrame '' (J.toSubgroup : Set _)).indicator (fun _ => (1 : ℂ)) M
  by_cases hM : M ∈ adjacentRankFrame '' (J.toSubgroup : Set _)
  · rw [Set.indicator_of_mem hM, Set.indicator_of_mem
      ((adjacentRankFrame_image_mul_iff J.toSubgroup k M).mpr hM)]
  · rw [Set.indicator_of_notMem hM, Set.indicator_of_notMem
      (fun hm => hM ((adjacentRankFrame_image_mul_iff J.toSubgroup k M).mp hm))]

theorem isOpen_adjacentRankFrameSlice {r : ℕ}
    (J : OpenSubgroup (GeneralLinear (r + 2) K)) :
    IsOpen (adjacentRankFrameSlice J.toSubgroup : Set (GeneralLinear (r + 1) K)) := by
  have he : (adjacentRankFrameSlice J.toSubgroup : Set (GeneralLinear (r + 1) K)) =
      (fun h : GeneralLinear (r + 1) K => rectangularJoin h.val 0) ⁻¹'
        (adjacentRankFrame '' (J : Set (GeneralLinear (r + 2) K))) :=
    Set.ext fun h => mem_adjacentRankFrameSlice_iff J.toSubgroup h
  rw [he]
  exact (isOpen_adjacentRankFrame_image J.toSubgroup J.isOpen).preimage
    (continuous_rectangularJoin.comp (Units.continuous_val.prodMk continuous_const))

/-- The inner slice is a compact open subgroup of the actual `GL_(r+1)`. -/
theorem isCompact_adjacentRankFrameSlice {r : ℕ}
    (J : OpenSubgroup (GeneralLinear (r + 2) K))
    (hJ : IsCompact (J : Set (GeneralLinear (r + 2) K))) :
    IsCompact (adjacentRankFrameSlice J.toSubgroup : Set (GeneralLinear (r + 1) K)) := by
  let Φ := adjacentRankFrameOrbitTest J hJ
  have hc := adjacentRankCompactOrbit_hasCompactSupport_one Φ.val Φ.property
  apply hc.of_isClosed_subset
    ((adjacentRankFrameSlice J.toSubgroup).isClosed_of_isOpen
      (isOpen_adjacentRankFrameSlice J))
  intro h hh
  apply subset_tsupport
  change Φ.val (rectangularJoin h.val 0) ≠ 0
  rw [adjacentRankFrameOrbitTest_apply]
  have hm : rectangularJoin h.val 0 ∈
      adjacentRankFrame '' (J : Set (GeneralLinear (r + 2) K)) :=
    (mem_adjacentRankFrameSlice_iff J.toSubgroup h).mp hh
  rw [Set.indicator_of_mem hm]
  exact one_ne_zero

end Topology

end Langlands.RankinSelberg
