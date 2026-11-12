import Langlands.GroupScheme.SymplecticMatrix.SimplyConnected

/-! # The roots of the split symplectic group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SymplecticMatrix

variable {l : Type} [Fintype l] [DecidableEq l]

/-! ### The short root vectors -/

section Entries

variable {A : Type*} [CommRing A]

/-- The matrix `E_{inl a, inl b} - E_{inr b, inr a}` satisfies the Lie condition of `Sp`. -/
theorem single_inl_inl_sub_single_inr_inr_mul_J_add (a b : l) :
    (Matrix.single (Sum.inl a) (Sum.inl b) (1 : A) - Matrix.single (Sum.inr b) (Sum.inr a) 1) *
        Matrix.J l A +
      Matrix.J l A * (Matrix.single (Sum.inl a) (Sum.inl b) (1 : A) -
        Matrix.single (Sum.inr b) (Sum.inr a) 1).transpose = 0 := by
  refine (lie_condition_iff _).mpr ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · simp [Matrix.sub_apply]
  · simp only [Matrix.sub_apply, Matrix.single_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
      and_false, ite_false, sub_zero, zero_sub]
    exact congrArg Neg.neg (if_congr and_comm rfl rfl)
  · simp [Matrix.sub_apply]

omit [Fintype l] in
/-- Every coordinate of a weight `w(x)` is `-1`, `0` or `1`. -/
theorem weightCoord_apply_mem_Icc (x : l ⊕ l) (a : l) :
    -1 ≤ weightCoord l x a ∧ weightCoord l x a ≤ 1 := by
  rcases x with b | b <;> simp only [weightCoord_inl, weightCoord_inr, Pi.single_apply] <;>
    split_ifs <;> omega

end Entries

/-! ### Roots over a field -/

section Field

variable {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)

/-- **Pairing with a long coroot.** If `P.root j` is the long root `2e_a`, then the pairing of
any root `P.root i` with `P.coroot j` is the `a`-th coordinate of `P.root i`. -/
theorem pairing_eq_coord_of_root_eq_longRoot {J : Type u}
    {P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)}
    (hP : IsRootDatumOf (diagonalTorus l (CommRingCat.of k)) P) {j : J} {a : l}
    (hj : P.root j = longRoot l k a) (i : J) :
    P.pairing i j = GeneralLinear.characterCoordEquiv l k (P.root i) a := by
  rw [← P.root_coroot_eq_pairing, hP.1, GeneralLinear.latticePairing_coord,
    cocharacterCoordEquiv_coroot_of_root_eq_longRoot hP hj,
    Finset.sum_eq_single a (fun c _ hc => by rw [Pi.single_eq_of_ne hc, mul_zero]) (by simp),
    Pi.single_eq_same, mul_one]

/-- Every coordinate of a root lies between `-2` and `2`. -/
theorem coord_mem_Icc_of_mem_roots {χ : characterLattice 𝔻}
    (hχ : χ ∈ roots (diagonalTorus l (CommRingCat.of k))) (a : l) :
    -2 ≤ GeneralLinear.characterCoordEquiv l k χ a ∧
      GeneralLinear.characterCoordEquiv l k χ a ≤ 2 := by
  obtain ⟨x, y, hxy⟩ := exists_coord_of_mem_roots hχ
  rw [hxy, Pi.sub_apply]
  have hx := weightCoord_apply_mem_Icc x a
  have hy := weightCoord_apply_mem_Icc y a
  omega

/-- The roots are stable under negation. -/
theorem neg_mem_roots {χ : characterLattice 𝔻}
    (hχ : χ ∈ roots (diagonalTorus l (CommRingCat.of k))) :
    -χ ∈ roots (diagonalTorus l (CommRingCat.of k)) := by
  obtain ⟨J, _, P, hP, -⟩ := exists_rootDatum l k
  rw [← hP.2.1] at hχ ⊢
  obtain ⟨j, rfl⟩ := hχ
  exact ⟨P.reflectionPerm j j, by rw [P.root_reflectionPerm, P.reflection_apply_self]⟩

variable (l k) in
/-- The short root `e_a - e_b`. -/
def diffRoot (a b : l) : characterLattice 𝔻 :=
  (GeneralLinear.characterCoordEquiv l k).symm (Pi.single a 1 - Pi.single b 1)

theorem characterCoordEquiv_diffRoot (a b : l) :
    GeneralLinear.characterCoordEquiv l k (diffRoot l k a b) = Pi.single a 1 - Pi.single b 1 :=
  LinearEquiv.apply_symm_apply _ _

variable (l k) in
/-- The short root `e_a + e_b`. -/
def sumRoot (a b : l) : characterLattice 𝔻 :=
  (GeneralLinear.characterCoordEquiv l k).symm (Pi.single a 1 + Pi.single b 1)

theorem characterCoordEquiv_sumRoot (a b : l) :
    GeneralLinear.characterCoordEquiv l k (sumRoot l k a b) = Pi.single a 1 + Pi.single b 1 :=
  LinearEquiv.apply_symm_apply _ _

/-- For `a ≠ b`, the short root `e_a - e_b` is a root, with root vector the matrix
`E_{inl a, inl b} - E_{inr b, inr a}`. -/
theorem diffRoot_mem_roots {a b : l} (hab : a ≠ b) :
    diffRoot l k a b ∈ roots (diagonalTorus l (CommRingCat.of k)) := by
  refine ⟨fun h0 => ?_, ?_⟩
  · have h1 := congrFun (characterCoordEquiv_diffRoot (k := k) a b) a
    rw [h0, map_zero, Pi.zero_apply, Pi.sub_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hab] at h1
    norm_num at h1
  · obtain ⟨X, hX⟩ := exists_lieMatrix_eq (R := CommRingCat.of k) _
      (single_inl_inl_sub_single_inr_inr_mul_J_add (A := k) a b)
    rw [Submodule.ne_bot_iff]
    refine ⟨X, ?_, fun h0 => ?_⟩
    · rw [mem_weightSpace_diagonalTorus_iff_support, hX, characterCoordEquiv_diffRoot]
      intro x y hxy
      rcases x with x | x <;> rcases y with y | y <;>
        simp [Matrix.sub_apply, Matrix.single_apply] at hxy
      · obtain ⟨rfl, rfl⟩ := hxy
        rfl
      · obtain ⟨rfl, rfl⟩ := hxy
        funext c
        simp only [Pi.sub_apply, weightCoord_inr, Pi.single_apply]
        split_ifs <;> omega
    · have h1 := congrArg (fun Y => lieMatrix Y (Sum.inl a) (Sum.inl b)) h0
      simp [hX, Matrix.sub_apply] at h1

/-- For `a ≠ b`, the short root `e_a + e_b` is a root: it is the reflection of `e_a - e_b` in
the long root `2e_b`. -/
theorem sumRoot_mem_roots {a b : l} (hab : a ≠ b) :
    sumRoot l k a b ∈ roots (diagonalTorus l (CommRingCat.of k)) := by
  obtain ⟨J, _, P, hP, -⟩ := exists_rootDatum l k
  obtain ⟨i, hi⟩ : diffRoot l k a b ∈ Set.range P.root := by
    rw [hP.2.1]
    exact diffRoot_mem_roots hab
  obtain ⟨j, hj⟩ : longRoot l k b ∈ Set.range P.root := by
    rw [hP.2.1]
    exact longRoot_mem_roots b
  rw [← hP.2.1]
  refine ⟨P.reflectionPerm j i, ?_⟩
  rw [P.root_reflectionPerm, P.reflection_apply_root, pairing_eq_coord_of_root_eq_longRoot hP hj,
    hi, hj]
  apply (GeneralLinear.characterCoordEquiv l k).injective
  rw [map_sub, map_zsmul, characterCoordEquiv_diffRoot, characterCoordEquiv_longRoot,
    characterCoordEquiv_sumRoot, Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm hab),
    Pi.single_eq_same]
  funext c
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> omega

/-- The weight difference `w(inl a) - w(inr b) = e_a + e_b` is a root, for all `a` and `b`. -/
theorem inl_sub_inr_mem_roots (a b : l) :
    (GeneralLinear.characterCoordEquiv l k).symm
        (weightCoord l (Sum.inl a) - weightCoord l (Sum.inr b)) ∈
      roots (diagonalTorus l (CommRingCat.of k)) := by
  by_cases hab : a = b
  · subst hab
    rw [weightCoord_inl_sub_inr]
    exact longRoot_mem_roots a
  · have h : weightCoord l (Sum.inl a) - weightCoord l (Sum.inr b) =
        Pi.single a 1 + Pi.single b 1 := by
      rw [weightCoord_inl, weightCoord_inr, Pi.single_neg, sub_neg_eq_add]
    rw [h]
    exact sumRoot_mem_roots hab

/-- **The roots of the diagonal torus.** A character is a root exactly when its coordinates
are a weight difference `w(x) - w(y)` with `x ≠ y`. In other words, the roots are the
characters with coordinates `±2e_a` and `±e_a ± e_b` for `a ≠ b`. -/
theorem mem_roots_iff (χ : characterLattice 𝔻) :
    χ ∈ roots (diagonalTorus l (CommRingCat.of k)) ↔
      ∃ x y : l ⊕ l, x ≠ y ∧
        GeneralLinear.characterCoordEquiv l k χ = weightCoord l x - weightCoord l y := by
  constructor
  · intro hχ
    obtain ⟨x, y, hxy⟩ := exists_coord_of_mem_roots hχ
    refine ⟨x, y, fun h => hχ.1 ?_, hxy⟩
    rw [h, sub_self] at hxy
    exact (GeneralLinear.characterCoordEquiv l k).map_eq_zero_iff.mp hxy
  · rintro ⟨x, y, hne, hχ⟩
    rw [← (GeneralLinear.characterCoordEquiv l k).symm_apply_apply χ, hχ]
    rcases x with a | a <;> rcases y with b | b
    · have hab : a ≠ b := fun h => hne (congrArg Sum.inl h)
      exact diffRoot_mem_roots hab
    · exact inl_sub_inr_mem_roots a b
    · rw [← neg_sub, map_neg]
      exact neg_mem_roots (inl_sub_inr_mem_roots b a)
    · have hab : b ≠ a := fun h => hne (congrArg Sum.inr h.symm)
      have h : weightCoord l (Sum.inr a) - weightCoord l (Sum.inr b) =
          Pi.single b 1 - Pi.single a 1 := by
        funext c
        simp only [Pi.sub_apply, weightCoord_inr, Pi.single_apply]
        split_ifs <;> omega
      rw [h]
      exact diffRoot_mem_roots hab

end Field

end Langlands.GroupScheme.SymplecticMatrix
