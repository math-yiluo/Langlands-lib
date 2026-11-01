import Langlands.Representation.Geometric.ClosedSubgroupDefinitions
import Langlands.Representation.Derivative.MinusVanishing
import Langlands.Group.GL.Maps
import Langlands.Group.GL.MirabolicMixedProductSubgroups
import Langlands.Group.GL.MirabolicOppositeIntersection

/-!
# The two mirabolic orbits on the binary-parabolic flag variety

For `P` the upper block parabolic of the binary shape `(m+1, n+1)` in
`GL_((m+1)+(n+1))` and `Q` the mirabolic subgroup, a coset `P g` lies in the
closed `Q`-orbit of `P` exactly when the last row of `g⁻¹` vanishes on the first
block, and otherwise in the open orbit of `P w⁻¹`, for an explicit permutation
matrix `w`. These two orbits, open one first, form an ordered double-coset
enumeration.
-/

noncomputable section

namespace Langlands.Derivative.MirabolicProductRestriction

open GeneralLinear GeneralLinear.Mirabolic.MixedProduct

universe u

section Algebra

variable {K : Type u} [Field K] (m n : ℕ)

/-- The binary block shape `(m+1, n+1)`. -/
abbrev shape : BlockShape ((m + 1) + (n + 1)) :=
  BlockShape.binary (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n)

variable (K) in
/-- The upper block parabolic of the binary shape `(m+1, n+1)`. -/
abbrev parabolicP : Subgroup (GeneralLinear ((m + 1) + (n + 1)) K) :=
  (shape m n).parabolic K

variable (K) in
/-- The mirabolic subgroup `P_((m+1)+(n+1))`, as a subgroup of the same group. -/
abbrev mirabolicQ : Subgroup (GeneralLinear ((m + 1) + (n + 1)) K) :=
  mirabolic ((m + 1) + n) K

theorem mem_parabolicP_iff (g : GeneralLinear ((m + 1) + (n + 1)) K) :
    g ∈ parabolicP K m n ↔ ∀ (i : Fin (n + 1)) (j : Fin (m + 1)),
      g.val (Fin.natAdd (m + 1) i) (Fin.castAdd (n + 1) j) = 0 := by
  rw [BlockShape.mem_parabolic_iff]
  constructor
  · intro h i j
    have e := h (1 : Fin 2) (0 : Fin 2) i j (show (0 : Fin 2) < 1 from by decide)
    exact (congrArg₂ g.val
      (BlockShape.binary_index_one (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n) i)
      (BlockShape.binary_index_zero (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n) j)).symm.trans e
  · intro h i j x y hij
    fin_cases i <;> fin_cases j
    · exact False.elim (lt_irrefl _ hij)
    · simp at hij
    · change g.val ((shape m n).index (1 : Fin 2) x) ((shape m n).index (0 : Fin 2) y) = 0
      exact (congrArg₂ g.val
        (BlockShape.binary_index_one (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n) x)
        (BlockShape.binary_index_zero (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n) y)).trans
          (h x y)
    · exact False.elim (lt_irrefl _ hij)

theorem mirabolicQ_row (q : GeneralLinear ((m + 1) + (n + 1)) K) (hq : q ∈ mirabolicQ K m n)
    (g : GeneralLinear ((m + 1) + (n + 1)) K) (j : Fin ((m + 1) + (n + 1))) :
    (q * g).val (Fin.last ((m + 1) + n)) j = g.val (Fin.last ((m + 1) + n)) j := by
  have hq' := (mem_mirabolic (n := (m + 1) + n) q).mp hq
  rw [Units.val_mul, Matrix.mul_apply]
  simp only [hq', ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Every row of an invertible matrix is nonzero. -/
theorem exists_row_ne_zero {k : ℕ} (g : GeneralLinear k K) (i : Fin k) :
    ∃ j, g.val i j ≠ 0 := by
  by_contra! h
  have h1 : (g.val * (g⁻¹).val) i i = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at h1
  simp [h] at h1

/-! ### Upper block matrices -/

/-- The block matrix `[h₀ x; 0 h₁]` in the consecutive coordinates. -/
def blockUpper (h₀ : GeneralLinear (m + 1) K) (h₁ : GeneralLinear (n + 1) K)
    (x : Matrix (Fin (m + 1)) (Fin (n + 1)) K) : GeneralLinear ((m + 1) + (n + 1)) K :=
  reindex finSumFinEquiv (TwoBlock.matrix h₀ h₁ x).val

theorem blockUpper_apply (h₀ : GeneralLinear (m + 1) K) (h₁ : GeneralLinear (n + 1) K)
    (x : Matrix (Fin (m + 1)) (Fin (n + 1)) K) (i j : Fin (m + 1) ⊕ Fin (n + 1)) :
    (blockUpper m n h₀ h₁ x).val (finSumFinEquiv i) (finSumFinEquiv j) =
      Matrix.fromBlocks h₀.val x 0 h₁.val i j := by
  change Matrix.fromBlocks h₀.val x 0 h₁.val (finSumFinEquiv.symm (finSumFinEquiv i))
    (finSumFinEquiv.symm (finSumFinEquiv j)) = _
  simp only [Equiv.symm_apply_apply]

@[simp] theorem blockUpper_castAdd_castAdd (h₀ : GeneralLinear (m + 1) K)
    (h₁ : GeneralLinear (n + 1) K) (x : Matrix (Fin (m + 1)) (Fin (n + 1)) K)
    (i j : Fin (m + 1)) :
    (blockUpper m n h₀ h₁ x).val (Fin.castAdd (n + 1) i) (Fin.castAdd (n + 1) j) =
      h₀.val i j := by
  simpa using blockUpper_apply m n h₀ h₁ x (Sum.inl i) (Sum.inl j)

@[simp] theorem blockUpper_castAdd_natAdd (h₀ : GeneralLinear (m + 1) K)
    (h₁ : GeneralLinear (n + 1) K) (x : Matrix (Fin (m + 1)) (Fin (n + 1)) K)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (blockUpper m n h₀ h₁ x).val (Fin.castAdd (n + 1) i) (Fin.natAdd (m + 1) j) = x i j := by
  simpa using blockUpper_apply m n h₀ h₁ x (Sum.inl i) (Sum.inr j)

@[simp] theorem blockUpper_natAdd_castAdd (h₀ : GeneralLinear (m + 1) K)
    (h₁ : GeneralLinear (n + 1) K) (x : Matrix (Fin (m + 1)) (Fin (n + 1)) K)
    (i : Fin (n + 1)) (j : Fin (m + 1)) :
    (blockUpper m n h₀ h₁ x).val (Fin.natAdd (m + 1) i) (Fin.castAdd (n + 1) j) = 0 := by
  simpa using blockUpper_apply m n h₀ h₁ x (Sum.inr i) (Sum.inl j)

@[simp] theorem blockUpper_natAdd_natAdd (h₀ : GeneralLinear (m + 1) K)
    (h₁ : GeneralLinear (n + 1) K) (x : Matrix (Fin (m + 1)) (Fin (n + 1)) K)
    (i j : Fin (n + 1)) :
    (blockUpper m n h₀ h₁ x).val (Fin.natAdd (m + 1) i) (Fin.natAdd (m + 1) j) =
      h₁.val i j := by
  simpa using blockUpper_apply m n h₀ h₁ x (Sum.inr i) (Sum.inr j)

theorem blockUpper_mem (h₀ : GeneralLinear (m + 1) K) (h₁ : GeneralLinear (n + 1) K)
    (x : Matrix (Fin (m + 1)) (Fin (n + 1)) K) :
    blockUpper m n h₀ h₁ x ∈ parabolicP K m n :=
  (mem_parabolicP_iff m n _).mpr fun i j => blockUpper_natAdd_castAdd m n h₀ h₁ x i j

/-! ### The open-orbit representative -/

/-- The coordinate permutation sending the first block to the mirabolic block
`(first m, last)` and the second block to the middle coordinates. -/
def openIndex : Equiv.Perm (Fin ((m + 1) + (n + 1))) :=
  (finSumFinEquiv.symm.trans (rightIndex (n + 1) m)).trans (finCongr (by omega))

@[simp] theorem openIndex_castAdd (j : Fin (m + 1)) :
    openIndex m n (Fin.castAdd (n + 1) j) =
      finCongr (by omega) (rightIndex (n + 1) m (Sum.inl j)) := by
  simp [openIndex]

@[simp] theorem openIndex_natAdd (i : Fin (n + 1)) :
    openIndex m n (Fin.natAdd (m + 1) i) =
      finCongr (by omega) (rightIndex (n + 1) m (Sum.inr i)) := by
  simp [openIndex]

theorem openIndex_corner :
    openIndex m n (Fin.castAdd (n + 1) (Fin.last m)) = Fin.last ((m + 1) + n) := by
  apply Fin.ext
  simp only [openIndex_castAdd, rightIndex_last, finCongr_apply, Fin.val_cast, Fin.val_last]
  omega

variable (K) in
/-- The permutation matrix `w` whose open-orbit coset is `P w⁻¹`. -/
def openRep : GeneralLinear ((m + 1) + (n + 1)) K :=
  permutation _ K (openIndex m n)

theorem openRep_lastRow (k : Fin ((m + 1) + (n + 1))) :
    (openRep K m n).val (Fin.last ((m + 1) + n)) k =
      if k = Fin.castAdd (n + 1) (Fin.last m) then 1 else 0 := by
  rw [openRep, permutation_entry]
  have : openIndex m n k = Fin.last ((m + 1) + n) ↔ k = Fin.castAdd (n + 1) (Fin.last m) := by
    rw [← openIndex_corner m n]
    exact (openIndex m n).injective.eq_iff
  simp only [this]

theorem openRep_mul_row (g : GeneralLinear ((m + 1) + (n + 1)) K) (j : Fin ((m + 1) + (n + 1))) :
    (openRep K m n * g).val (Fin.last ((m + 1) + n)) j =
      g.val (Fin.castAdd (n + 1) (Fin.last m)) j := by
  rw [Units.val_mul, Matrix.mul_apply]
  simp only [openRep_lastRow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

/-- Conjugation `w⁻¹ g w` reads entries along `openIndex`. -/
theorem openRep_conj_apply (g : GeneralLinear ((m + 1) + (n + 1)) K)
    (x y : Fin ((m + 1) + (n + 1))) :
    ((openRep K m n)⁻¹ * g * openRep K m n).val x y =
      g.val (openIndex m n x) (openIndex m n y) := by
  have e : openRep K m n = (permutation _ K (openIndex m n)⁻¹)⁻¹ := by
    rw [permutation_inv, inv_inv]
    rfl
  rw [e, inv_inv]
  have h := permutation_conjugate_entry _ K (openIndex m n)⁻¹ g x y
  simpa only [inv_inv] using h

/-! ### The closed-cell invariant -/

/-- The last row of `g⁻¹`. -/
def lastInvRow (g : GeneralLinear ((m + 1) + (n + 1)) K) (j : Fin ((m + 1) + (n + 1))) : K :=
  (g⁻¹).val (Fin.last ((m + 1) + n)) j

/-- The last row of `g⁻¹` vanishes on the first block. -/
def IsClosedCell (g : GeneralLinear ((m + 1) + (n + 1)) K) : Prop :=
  ∀ i : Fin (m + 1), lastInvRow m n g (Fin.castAdd (n + 1) i) = 0

theorem mul_row_of_row_eq (A g : GeneralLinear ((m + 1) + (n + 1)) K)
    (r : Fin ((m + 1) + (n + 1))) (hA : ∀ k, A.val r k = lastInvRow m n g k)
    (j : Fin ((m + 1) + (n + 1))) :
    (A * g).val r j = if j = Fin.last ((m + 1) + n) then 1 else 0 := by
  have h1 : (g⁻¹ * g).val (Fin.last ((m + 1) + n)) j =
      (1 : GeneralLinear ((m + 1) + (n + 1)) K).val (Fin.last ((m + 1) + n)) j := by
    rw [inv_mul_cancel]
  rw [Units.val_mul, Matrix.mul_apply] at h1 ⊢
  simp only [hA, lastInvRow]
  rw [h1, Units.val_one, Matrix.one_apply]
  by_cases hj : j = Fin.last ((m + 1) + n)
  · subst hj
    simp
  · simp [hj, Ne.symm hj]

theorem isClosedCell_mul (p q : GeneralLinear ((m + 1) + (n + 1)) K)
    (hp : p ∈ parabolicP K m n) (hq : q ∈ mirabolicQ K m n) :
    IsClosedCell m n (p * q) := by
  intro i
  unfold lastInvRow
  rw [mul_inv_rev, mirabolicQ_row m n _ (inv_mem hq)]
  exact (mem_parabolicP_iff m n _).mp (inv_mem hp) (Fin.last n) i

theorem not_isClosedCell_mul (p q : GeneralLinear ((m + 1) + (n + 1)) K)
    (hp : p ∈ parabolicP K m n) (hq : q ∈ mirabolicQ K m n) :
    ¬ IsClosedCell m n (p * (openRep K m n)⁻¹ * q) := by
  intro h
  obtain ⟨j, hj⟩ := exists_row_ne_zero (k := m + 1)
    ((shape m n).leviProjection K ⟨p⁻¹, inv_mem hp⟩ (0 : Fin 2)) (Fin.last m)
  apply hj
  have hc := h j
  unfold lastInvRow at hc
  rw [mul_inv_rev, mul_inv_rev, inv_inv, mirabolicQ_row m n _ (inv_mem hq),
    openRep_mul_row] at hc
  exact (congrArg₂ (p⁻¹).val
    (BlockShape.binary_index_zero (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n) (Fin.last m))
    (BlockShape.binary_index_zero (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n) j)).trans hc

theorem exists_eq_mul_of_isClosedCell (g : GeneralLinear ((m + 1) + (n + 1)) K)
    (h : IsClosedCell m n g) :
    ∃ p ∈ parabolicP K m n, ∃ q ∈ mirabolicQ K m n, g = p * q := by
  have hu : (fun j : Fin (n + 1) => lastInvRow m n g (Fin.natAdd (m + 1) j)) ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := exists_row_ne_zero g⁻¹ (Fin.last ((m + 1) + n))
    apply hk
    induction k using Fin.addCases with
    | left i => exact h i
    | right i => exact congrFun h0 i
  obtain ⟨b, hb⟩ := Langlands.Derivative.Mirabolic.exists_lastRow_eq_of_ne_zero _ hu
  refine ⟨(blockUpper m n 1 b 0)⁻¹, inv_mem (blockUpper_mem m n _ _ _),
    blockUpper m n 1 b 0 * g, ?_, (inv_mul_cancel_left _ _).symm⟩
  rw [mem_mirabolic (n := (m + 1) + n)]
  intro j
  apply mul_row_of_row_eq
  intro k
  rw [← Fin.natAdd_last]
  induction k using Fin.addCases with
  | left i =>
    rw [blockUpper_natAdd_castAdd]
    exact (h i).symm
  | right i =>
    rw [blockUpper_natAdd_natAdd]
    exact congrFun hb i

theorem exists_eq_mul_openRep_of_not_isClosedCell (g : GeneralLinear ((m + 1) + (n + 1)) K)
    (h : ¬ IsClosedCell m n g) :
    ∃ p ∈ parabolicP K m n, ∃ q ∈ mirabolicQ K m n, g = p * (openRep K m n)⁻¹ * q := by
  have hu : (fun i : Fin (m + 1) => lastInvRow m n g (Fin.castAdd (n + 1) i)) ≠ 0 := by
    intro h0
    exact h fun i => congrFun h0 i
  obtain ⟨a, ha⟩ := Langlands.Derivative.Mirabolic.exists_lastRow_eq_of_ne_zero _ hu
  let x : Matrix (Fin (m + 1)) (Fin (n + 1)) K := fun i j =>
    if i = Fin.last m then lastInvRow m n g (Fin.natAdd (m + 1) j) else 0
  refine ⟨(blockUpper m n a 1 x)⁻¹, inv_mem (blockUpper_mem m n _ _ _),
    openRep K m n * blockUpper m n a 1 x * g, ?_, by group⟩
  rw [mem_mirabolic (n := (m + 1) + n)]
  intro j
  rw [mul_assoc, openRep_mul_row]
  apply mul_row_of_row_eq
  intro k
  induction k using Fin.addCases with
  | left i =>
    rw [blockUpper_castAdd_castAdd]
    exact congrFun ha i
  | right i =>
    rw [blockUpper_castAdd_natAdd]
    simp [x]

end Algebra

/-! ### Orbits and their ordering -/

section Orbits

variable {G : Type u} [Group G]

theorem mem_cosetOrbit_iff (P Q : Subgroup G) (w g : G) :
    Induction.quotientMap P g ∈ Geometric.cosetOrbit P Q w ↔
      ∃ p ∈ P, ∃ q ∈ Q, g = p * w⁻¹ * q := by
  constructor
  · rintro ⟨q, hq⟩
    have hr := QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
    refine ⟨g * (w⁻¹ * (q : G))⁻¹, hr, q, q.property, ?_⟩
    group
  · rintro ⟨p, hp, q, hq, rfl⟩
    refine ⟨⟨q, hq⟩, Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)⟩
    simpa [mul_assoc] using hp

end Orbits

section Ordering

variable {K : Type u} [Field K] (m n : ℕ)

theorem mem_closedOrbit_iff (g : GeneralLinear ((m + 1) + (n + 1)) K) :
    Induction.quotientMap (parabolicP K m n) g ∈
        Geometric.cosetOrbit (parabolicP K m n) (mirabolicQ K m n) 1 ↔
      IsClosedCell m n g := by
  rw [mem_cosetOrbit_iff]
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    simpa using isClosedCell_mul m n p q hp hq
  · intro h
    obtain ⟨p, hp, q, hq, rfl⟩ := exists_eq_mul_of_isClosedCell m n g h
    exact ⟨p, hp, q, hq, by simp⟩

theorem mem_openOrbit_iff (g : GeneralLinear ((m + 1) + (n + 1)) K) :
    Induction.quotientMap (parabolicP K m n) g ∈
        Geometric.cosetOrbit (parabolicP K m n) (mirabolicQ K m n) (openRep K m n) ↔
      ¬ IsClosedCell m n g := by
  rw [mem_cosetOrbit_iff]
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact not_isClosedCell_mul m n p q hp hq
  · exact exists_eq_mul_openRep_of_not_isClosedCell m n g

variable [TopologicalSpace K] [IsTopologicalRing K] [T1Space K]

omit [IsTopologicalRing K] in
theorem isOpen_openOrbit :
    IsOpen (Geometric.cosetOrbit (parabolicP K m n) (mirabolicQ K m n) (openRep K m n)) := by
  have hq : Topology.IsQuotientMap (Induction.quotientMap (parabolicP K m n)) :=
    isQuotientMap_quotient_mk'
  rw [← hq.isOpen_preimage]
  have e : (Induction.quotientMap (parabolicP K m n) ⁻¹' Geometric.cosetOrbit (parabolicP K m n) (mirabolicQ K m n)
      (openRep K m n)) = ⋃ i : Fin (m + 1),
        {g : GeneralLinear ((m + 1) + (n + 1)) K | lastInvRow m n g (Fin.castAdd (n + 1) i) ≠ 0} := by
    ext g
    rw [Set.mem_preimage, mem_openOrbit_iff]
    simp [IsClosedCell]
  rw [e]
  refine isOpen_iUnion fun i => ?_
  exact isOpen_compl_singleton.preimage
    (Units.continuous_coe_inv.matrix_elem (Fin.last ((m + 1) + n)) (Fin.castAdd (n + 1) i))

/-- The open orbit of `P w⁻¹`, then the closed orbit of `P`. -/
def orbitOrdering :
    Geometric.OrderedDoubleCosets (parabolicP K m n) (mirabolicQ K m n) 2 where
  representative := ![openRep K m n, 1]
  covers x := by
    induction x using Quotient.inductionOn with
    | h g =>
      by_cases hg : IsClosedCell m n g
      · exact ⟨1, (mem_closedOrbit_iff m n g).mpr hg⟩
      · exact ⟨0, (mem_openOrbit_iff m n g).mpr hg⟩
  disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hi hj
    induction x using Quotient.inductionOn with
    | h g =>
      fin_cases i <;> fin_cases j
      · exact hij rfl
      · exact (mem_openOrbit_iff m n g).mp hi ((mem_closedOrbit_iff m n g).mp hj)
      · exact (mem_openOrbit_iff m n g).mp hj ((mem_closedOrbit_iff m n g).mp hi)
      · exact hij rfl
  initial_open k := by
    fin_cases k
    · convert isOpen_empty
      ext x
      simp
    · convert isOpen_openOrbit (K := K) m n
      ext x
      constructor
      · rintro ⟨i, hi, hx⟩
        have : i = 0 := Fin.ext (by simpa using hi)
        subst this
        simpa using hx
      · intro hx
        exact ⟨0, by simp, by simpa using hx⟩
    · convert isOpen_univ
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      induction x using Quotient.inductionOn with
      | h g =>
        by_cases hg : IsClosedCell m n g
        · exact ⟨1, by simp, (mem_closedOrbit_iff m n g).mpr hg⟩
        · exact ⟨0, by simp, (mem_openOrbit_iff m n g).mpr hg⟩

@[simp] theorem orbitOrdering_representative_zero :
    (orbitOrdering (K := K) m n).representative 0 = openRep K m n := rfl

@[simp] theorem orbitOrdering_representative_one :
    (orbitOrdering (K := K) m n).representative 1 = 1 := rfl

end Ordering

end Langlands.Derivative.MirabolicProductRestriction
