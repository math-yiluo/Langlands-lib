import Langlands.GroupScheme.SymplecticMatrix.Torus
import Langlands.GroupScheme.Torus.SelfCentralizingFromLie
import Langlands.GroupScheme.Lie.SplitTorusCoordinates

/-! # Maximality of the diagonal torus of `Sp` and its long roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SymplecticMatrix

variable {l : Type} [Fintype l] [DecidableEq l]

/-! ### The Lie condition in entries -/

section Entries

variable {A : Type*} [CommRing A]

@[simp] theorem mul_J_apply_inl (Y : Matrix (l ⊕ l) (l ⊕ l) A) (x : l ⊕ l) (j : l) :
    (Y * Matrix.J l A) x (Sum.inl j) = Y x (Sum.inr j) := by
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

@[simp] theorem mul_J_apply_inr (Y : Matrix (l ⊕ l) (l ⊕ l) A) (x : l ⊕ l) (j : l) :
    (Y * Matrix.J l A) x (Sum.inr j) = -Y x (Sum.inl j) := by
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

@[simp] theorem J_mul_apply_inl (M : Matrix (l ⊕ l) (l ⊕ l) A) (i : l) (y : l ⊕ l) :
    (Matrix.J l A * M) (Sum.inl i) y = -M (Sum.inr i) y := by
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

@[simp] theorem J_mul_apply_inr (M : Matrix (l ⊕ l) (l ⊕ l) A) (i : l) (y : l ⊕ l) :
    (Matrix.J l A * M) (Sum.inr i) y = M (Sum.inl i) y := by
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

/-- `Y J + J Yᵀ = 0` exactly when, in blocks `Y = [[a, b], [c, d]]`, `b` and `c` are symmetric
and `d = -aᵀ`. -/
theorem lie_condition_iff (Y : Matrix (l ⊕ l) (l ⊕ l) A) :
    Y * Matrix.J l A + Matrix.J l A * Y.transpose = 0 ↔
      (∀ i j, Y (Sum.inl i) (Sum.inr j) = Y (Sum.inl j) (Sum.inr i)) ∧
      (∀ i j, Y (Sum.inr i) (Sum.inr j) = -Y (Sum.inl j) (Sum.inl i)) ∧
      (∀ i j, Y (Sum.inr i) (Sum.inl j) = Y (Sum.inr j) (Sum.inl i)) := by
  constructor
  · intro h
    have e : ∀ x y, (Y * Matrix.J l A + Matrix.J l A * Y.transpose) x y = 0 :=
      fun x y => by rw [h]; rfl
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · have h1 := e (Sum.inl i) (Sum.inl j)
      simp only [Matrix.add_apply, mul_J_apply_inl, J_mul_apply_inl, Matrix.transpose_apply] at h1
      linear_combination h1
    · have h1 := e (Sum.inr i) (Sum.inl j)
      simp only [Matrix.add_apply, mul_J_apply_inl, J_mul_apply_inr, Matrix.transpose_apply] at h1
      linear_combination h1
    · have h1 := e (Sum.inr i) (Sum.inr j)
      simp only [Matrix.add_apply, mul_J_apply_inr, J_mul_apply_inr, Matrix.transpose_apply] at h1
      linear_combination -h1
  · rintro ⟨hB, hD, hC⟩
    ext x y
    cases x with
    | inl i =>
      cases y with
      | inl j =>
        simp only [Matrix.add_apply, mul_J_apply_inl, J_mul_apply_inl, Matrix.transpose_apply,
          Matrix.zero_apply]
        rw [hB]
        ring
      | inr j =>
        simp only [Matrix.add_apply, mul_J_apply_inr, J_mul_apply_inl, Matrix.transpose_apply,
          Matrix.zero_apply]
        rw [hD]
        ring
    | inr i =>
      cases y with
      | inl j =>
        simp only [Matrix.add_apply, mul_J_apply_inl, J_mul_apply_inr, Matrix.transpose_apply,
          Matrix.zero_apply]
        rw [hD]
        ring
      | inr j =>
        simp only [Matrix.add_apply, mul_J_apply_inr, J_mul_apply_inr, Matrix.transpose_apply,
          Matrix.zero_apply]
        rw [hC]
        ring

/-- The diagonal matrix `diag(d, -d)` satisfies the Lie condition of `Sp`. -/
theorem diagonal_mul_J_add (d : l → A) :
    Matrix.diagonal (Sum.elim d (fun a => -d a)) * Matrix.J l A +
      Matrix.J l A * (Matrix.diagonal (Sum.elim d (fun a => -d a))).transpose = 0 := by
  refine (lie_condition_iff _).mpr ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · rw [Matrix.diagonal_apply_ne _ Sum.inl_ne_inr, Matrix.diagonal_apply_ne _ Sum.inl_ne_inr]
  · by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Sum.elim_inr, Sum.elim_inl]
    · rw [Matrix.diagonal_apply_ne _ (fun h => hij (Sum.inr_injective h)),
        Matrix.diagonal_apply_ne _ (fun h => hij (Sum.inl_injective h).symm), neg_zero]
  · rw [Matrix.diagonal_apply_ne _ Sum.inr_ne_inl, Matrix.diagonal_apply_ne _ Sum.inr_ne_inl]

end Entries

/-! ### Coordinates of weight differences -/

section Coords

omit [Fintype l] in
/-- A weight difference `w(x) - w(y)` with coordinate `2` at `b` comes from `x = inl b` and
`y = inr b`. -/
theorem eq_of_weightCoord_sub_apply_eq_two {x y : l ⊕ l} {b : l}
    (h : (weightCoord l x - weightCoord l y) b = 2) : x = Sum.inl b ∧ y = Sum.inr b := by
  cases x with
  | inl a =>
    cases y with
    | inl c =>
      simp only [Pi.sub_apply, weightCoord_inl, Pi.single_apply] at h
      split_ifs at h <;> omega
    | inr c =>
      simp only [Pi.sub_apply, weightCoord_inl, weightCoord_inr, Pi.single_apply] at h
      split_ifs at h with h1 h2 <;> first | omega | (subst h1; subst h2; exact ⟨rfl, rfl⟩)
  | inr a =>
    cases y with
    | inl c =>
      simp only [Pi.sub_apply, weightCoord_inl, weightCoord_inr, Pi.single_apply] at h
      split_ifs at h <;> omega
    | inr c =>
      simp only [Pi.sub_apply, weightCoord_inr, Pi.single_apply] at h
      split_ifs at h <;> omega

omit [Fintype l] in
theorem weightCoord_inl_sub_inr (b : l) :
    weightCoord l (Sum.inl b) - weightCoord l (Sum.inr b) = Pi.single b 2 := by
  rw [weightCoord_inl, weightCoord_inr, ← Pi.single_sub]
  norm_num

end Coords

/-! ### Maximality and roots over a field -/

section Field

variable {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)

/-- The zero weight space consists of the Lie algebra elements with diagonal matrix. -/
theorem mem_weightSpace_zero_iff
    (X : Additive (lieKernel (groupScheme l (CommRingCat.of k)) k)) :
    X ∈ weightSpace (diagonalTorus l (CommRingCat.of k)) 0 ↔
      ∀ x y : l ⊕ l, x ≠ y → lieMatrix X x y = 0 := by
  rw [mem_weightSpace_diagonalTorus_iff_support, map_zero]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  have hw : (0 : l → ℤ) = weightCoord l x - weightCoord l y ↔ x = y := by
    rw [eq_comm, sub_eq_zero]
    exact weightCoord_injective.eq_iff
  rw [hw]
  exact not_imp_comm

variable (l k) in
/-- The upper-left diagonal entries of an element of the zero weight space. -/
def zeroWeightCoord :
    weightSpace (diagonalTorus l (CommRingCat.of k)) 0 →ₗ[k] (l → k) where
  toFun X a := lieMatrix (X : Additive (lieKernel (groupScheme l (CommRingCat.of k)) k))
    (Sum.inl a) (Sum.inl a)
  map_add' X Y := by
    funext a
    simp only [Submodule.coe_add, map_add, Matrix.add_apply, Pi.add_apply]
  map_smul' c X := by
    funext a
    simp only [Submodule.coe_smul, map_smul, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
      RingHom.id_apply]

theorem zeroWeightCoord_apply (X : weightSpace (diagonalTorus l (CommRingCat.of k)) 0) (a : l) :
    zeroWeightCoord l k X a =
      lieMatrix (X : Additive (lieKernel (groupScheme l (CommRingCat.of k)) k))
        (Sum.inl a) (Sum.inl a) :=
  rfl

/-- An element of the zero weight space is determined by its diagonal entries `X_{aa}`, `a ∈ l`. -/
theorem lieMatrix_eq_zero_of_zeroWeightCoord
    (X : weightSpace (diagonalTorus l (CommRingCat.of k)) 0) (hX : zeroWeightCoord l k X = 0) :
    lieMatrix (X : Additive (lieKernel (groupScheme l (CommRingCat.of k)) k)) = 0 := by
  obtain ⟨Xv, hXv⟩ := X
  have hd : ∀ x y : l ⊕ l, x ≠ y → lieMatrix Xv x y = 0 := (mem_weightSpace_zero_iff Xv).mp hXv
  have hl := (lie_condition_iff (lieMatrix Xv)).mp (lieMatrix_mul_J_add Xv)
  have h0 : ∀ a, lieMatrix Xv (Sum.inl a) (Sum.inl a) = 0 := fun a => by
    have h := congrFun hX a
    rw [zeroWeightCoord_apply, Pi.zero_apply] at h
    exact h
  change lieMatrix Xv = 0
  ext x y
  rw [Matrix.zero_apply]
  by_cases hxy : x = y
  · subst hxy
    cases x with
    | inl a => exact h0 a
    | inr a => rw [hl.2.1 a a, h0 a, neg_zero]
  · exact hd x y hxy

theorem zeroWeightCoord_bijective : Function.Bijective (zeroWeightCoord l k) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro X hX
    apply Subtype.ext
    apply lieMatrix_injective (R := CommRingCat.of k) (A := k)
    rw [lieMatrix_eq_zero_of_zeroWeightCoord X hX, Submodule.coe_zero, map_zero]
  · intro d
    obtain ⟨X, hX⟩ := exists_lieMatrix_eq (R := CommRingCat.of k) _ (diagonal_mul_J_add d)
    have hmem : X ∈ weightSpace (diagonalTorus l (CommRingCat.of k)) 0 := by
      rw [mem_weightSpace_zero_iff, hX]
      intro x y hxy
      exact Matrix.diagonal_apply_ne _ hxy
    refine ⟨⟨X, hmem⟩, ?_⟩
    funext a
    rw [zeroWeightCoord_apply]
    change lieMatrix X (Sum.inl a) (Sum.inl a) = d a
    rw [hX, Matrix.diagonal_apply_eq, Sum.elim_inl]

/-- The zero weight space of the diagonal torus has dimension `|l|`. -/
theorem finrank_weightSpace_zero :
    Module.finrank k (weightSpace (diagonalTorus l (CommRingCat.of k)) 0) = Fintype.card l := by
  rw [(LinearEquiv.ofBijective (zeroWeightCoord l k) zeroWeightCoord_bijective).finrank_eq,
    Module.finrank_fintype_fun_eq_card]

variable (l k) in
/-- **Maximality.** The diagonal torus of `Sp_{2l}` over a field is a maximal torus. -/
theorem isMaximalTorus_diagonalTorus :
    IsMaximalTorus (diagonalTorus l (CommRingCat.of k)) := by
  have := connectedSpace_groupScheme l k
  have : IsAffineHom (𝔻).toGrp.X.hom := isAffineHom_splitTorus _ _
  refine isMaximalTorus_of_finrank_zeroWeight _ (isSplitTorus_diagonalTorus l k)
    (isClosedSubgroup_diagonalTorus l k) ?_
  rw [finrank_weightSpace_zero]
  have h := splitTorus.finrank_lieKernel (ULift.{u} l) k
  rw [Nat.card_ulift, Nat.card_eq_fintype_card] at h
  exact h.symm

/-! ### Long roots -/

/-- Every root of the diagonal torus is a weight difference `w(x) - w(y)`. -/
theorem exists_coord_of_mem_roots {χ : characterLattice 𝔻}
    (hχ : χ ∈ roots (diagonalTorus l (CommRingCat.of k))) :
    ∃ x y : l ⊕ l, GeneralLinear.characterCoordEquiv l k χ = weightCoord l x - weightCoord l y := by
  obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ.2
  obtain ⟨x, y, hxy⟩ : ∃ x y, lieMatrix X x y ≠ 0 := by
    by_contra h
    apply hX0
    apply lieMatrix_injective (R := CommRingCat.of k) (A := k)
    rw [map_zero]
    refine Matrix.ext fun x y => ?_
    rw [Matrix.zero_apply]
    by_contra hne
    exact h ⟨x, y, hne⟩
  exact ⟨x, y, (mem_weightSpace_diagonalTorus_iff_support X χ).mp hX x y hxy⟩

/-- A root with coordinate `2` at `b` is the long root `2 e_b`. -/
theorem eq_single_two_of_mem_roots {χ : characterLattice 𝔻}
    (hχ : χ ∈ roots (diagonalTorus l (CommRingCat.of k))) {b : l}
    (hb : GeneralLinear.characterCoordEquiv l k χ b = 2) :
    GeneralLinear.characterCoordEquiv l k χ = Pi.single b 2 := by
  obtain ⟨x, y, hxy⟩ := exists_coord_of_mem_roots hχ
  rw [hxy] at hb ⊢
  obtain ⟨rfl, rfl⟩ := eq_of_weightCoord_sub_apply_eq_two hb
  exact weightCoord_inl_sub_inr b

variable (l k) in
/-- The long root `2 e_a`. -/
def longRoot (a : l) : characterLattice 𝔻 :=
  (GeneralLinear.characterCoordEquiv l k).symm (Pi.single a 2)

theorem characterCoordEquiv_longRoot (a : l) :
    GeneralLinear.characterCoordEquiv l k (longRoot l k a) = Pi.single a 2 :=
  LinearEquiv.apply_symm_apply _ _

/-- The matrix unit at `(inl a, inr a)` satisfies the Lie condition of `Sp`. -/
theorem single_inl_inr_mul_J_add (a : l) :
    Matrix.single (Sum.inl a) (Sum.inr a) (1 : k) * Matrix.J l k +
      Matrix.J l k * (Matrix.single (Sum.inl a) (Sum.inr a) (1 : k)).transpose = 0 := by
  refine (lie_condition_iff _).mpr ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · rw [Matrix.single_apply, Matrix.single_apply]
    simp only [Sum.inl.injEq, Sum.inr.injEq]
    exact if_congr and_comm rfl rfl
  · rw [Matrix.single_apply_of_row_ne Sum.inl_ne_inr, Matrix.single_apply_of_col_ne _ _
      Sum.inr_ne_inl, neg_zero]
  · rw [Matrix.single_apply_of_row_ne Sum.inl_ne_inr, Matrix.single_apply_of_row_ne Sum.inl_ne_inr]

/-- The long root `2 e_a` is a root, with root vector the matrix unit at `(inl a, inr a)`. -/
theorem longRoot_mem_roots (a : l) : longRoot l k a ∈ roots (diagonalTorus l (CommRingCat.of k)) := by
  refine ⟨fun h0 => ?_, ?_⟩
  · have h1 := congrFun (characterCoordEquiv_longRoot (k := k) a) a
    rw [h0, map_zero, Pi.zero_apply, Pi.single_eq_same] at h1
    norm_num at h1
  · obtain ⟨X, hX⟩ := exists_lieMatrix_eq (R := CommRingCat.of k) _ (single_inl_inr_mul_J_add (k := k) a)
    rw [Submodule.ne_bot_iff]
    refine ⟨X, ?_, fun h0 => ?_⟩
    · rw [mem_weightSpace_diagonalTorus_iff_support, hX, characterCoordEquiv_longRoot]
      intro x y hxy
      obtain ⟨rfl, rfl⟩ : x = Sum.inl a ∧ y = Sum.inr a := by
        by_contra h
        exact hxy (Matrix.single_apply_of_ne _ _ _ _ _ fun e => h ⟨e.1.symm, e.2.symm⟩)
      exact (weightCoord_inl_sub_inr a).symm
    · have h1 := congrArg (fun Y => lieMatrix Y (Sum.inl a) (Sum.inr a)) h0
      simp only [hX, map_zero, Matrix.single_apply_same, Matrix.zero_apply] at h1
      exact one_ne_zero h1

end Field

end Langlands.GroupScheme.SymplecticMatrix
