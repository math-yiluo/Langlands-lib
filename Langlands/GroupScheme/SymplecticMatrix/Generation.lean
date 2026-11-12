import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.SymplecticGroup

/-! # Generation and irreducibility of symplectic matrix groups

For the standard alternating matrix `J = [[0, -1], [1, 0]]` on `l ⊕ l`, this module introduces
the block matrices

* `upper Y = [[1, Y], [0, 1]]` and `lower Z = [[1, 0], [Z, 1]]`, symplectic for symmetric
  `Y` and `Z`;
* `levi A = [[A, 0], [0, (A⁻¹)ᵀ]]`, symplectic for every invertible `A`;
* the symplectic transvections `transvection u = 1 + u (uᵀ J)`.

Over a field every symplectic matrix is a product `upper X * lower Z * levi A * upper Y`
(`exists_eq_upper_mul_lower_mul_levi_mul_upper`), and the symplectic group acts irreducibly on
the column space (`eq_top_of_forall_mulVec_mem`).
-/

noncomputable section

open Matrix

namespace Langlands.GroupScheme.SymplecticMatrix

variable {l : Type} [Fintype l] [DecidableEq l]

section Ring

variable {S T : Type*} [CommRing S] [CommRing T]

/-- The upper unipotent block matrix `[[1, Y], [0, 1]]`. -/
def upper (Y : Matrix l l S) : Matrix (l ⊕ l) (l ⊕ l) S :=
  fromBlocks 1 Y 0 1

/-- The lower unipotent block matrix `[[1, 0], [Z, 1]]`. -/
def lower (Z : Matrix l l S) : Matrix (l ⊕ l) (l ⊕ l) S :=
  fromBlocks 1 0 Z 1

/-- The Levi block matrix `[[A, 0], [0, (A⁻¹)ᵀ]]` of an invertible matrix `A`. -/
def levi (A : GL l S) : Matrix (l ⊕ l) (l ⊕ l) S :=
  fromBlocks (A : Matrix l l S) 0 0 ((A⁻¹ : GL l S) : Matrix l l S)ᵀ

theorem upper_mem {Y : Matrix l l S} (hY : Y.IsSymm) : upper Y ∈ symplecticGroup l S := by
  rw [upper, SymplecticGroup.fromBlocks_mem_iff]
  refine ⟨by simp, ?_, by simp⟩
  rw [hY.eq]
  simp

theorem lower_mem {Z : Matrix l l S} (hZ : Z.IsSymm) : lower Z ∈ symplecticGroup l S := by
  rw [lower, SymplecticGroup.fromBlocks_mem_iff]
  refine ⟨?_, by simp, by simp⟩
  rw [hZ.eq]
  simp

theorem levi_mem (A : GL l S) : levi A ∈ symplecticGroup l S := by
  rw [levi, SymplecticGroup.fromBlocks_mem_iff]
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_zero, sub_zero, ← transpose_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, transpose_one]

theorem upper_mul_upper (Y Y' : Matrix l l S) : upper Y * upper Y' = upper (Y + Y') := by
  simp [upper, fromBlocks_multiply, add_comm]

theorem lower_mul_lower (Z Z' : Matrix l l S) : lower Z * lower Z' = lower (Z + Z') := by
  simp [lower, fromBlocks_multiply, add_comm]

theorem levi_mul (A B : GL l S) : levi (A * B) = levi A * levi B := by
  simp [levi, fromBlocks_multiply, _root_.mul_inv_rev, transpose_mul]

omit [Fintype l] in
theorem upper_zero : upper (0 : Matrix l l S) = 1 := by
  simp [upper, fromBlocks_one]

omit [Fintype l] in
theorem lower_zero : lower (0 : Matrix l l S) = 1 := by
  simp [lower, fromBlocks_one]

omit [Fintype l] in
theorem map_upper (f : S →+* T) (Y : Matrix l l S) :
    (upper Y).map f = upper (Y.map f) := by
  simp [upper, fromBlocks_map]

omit [Fintype l] in
theorem map_lower (f : S →+* T) (Z : Matrix l l S) :
    (lower Z).map f = lower (Z.map f) := by
  simp [lower, fromBlocks_map]

theorem map_levi (f : S →+* T) (A : GL l S) :
    (levi A).map f = levi (Matrix.GeneralLinearGroup.map f A) := by
  rw [levi, levi, fromBlocks_map, ← map_inv, Matrix.map_zero _ (map_zero f), transpose_map]
  rfl

/-- The symplectic transvection `1 + u (uᵀ J)`, acting by `w ↦ w + (uᵀ J w) u`. -/
def transvection (u : l ⊕ l → S) : Matrix (l ⊕ l) (l ⊕ l) S :=
  1 + vecMulVec u (u ᵥ* J l S)

/-- The standard symplectic form is alternating. -/
theorem dotProduct_vecMul_J_self (u : l ⊕ l → S) : u ⬝ᵥ (u ᵥ* J l S) = 0 := by
  have h : u ᵥ* J l S = Sum.elim (u ∘ Sum.inr) (-(u ∘ Sum.inl)) := by
    ext (a | a) <;> simp [J, vecMul_fromBlocks, vecMul_neg, vecMul_one]
  rw [h, dotProduct, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Pi.neg_apply, mul_neg,
    Finset.sum_neg_distrib]
  rw [add_neg_eq_zero]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem transvection_mem (u : l ⊕ l → S) : transvection u ∈ symplecticGroup l S := by
  rw [SymplecticGroup.mem_iff, transvection, transpose_add, transpose_one,
    transpose_vecMulVec]
  have hNJ : vecMulVec u (u ᵥ* J l S) * J l S = -vecMulVec u u := by
    rw [vecMulVec_mul, vecMul_vecMul, J_squared, vecMul_neg, vecMul_one, vecMulVec_neg]
  have hJN : J l S * vecMulVec (u ᵥ* J l S) u = vecMulVec u u := by
    have h := congrArg Matrix.transpose hNJ
    rw [transpose_mul, transpose_vecMulVec, J_transpose, transpose_neg,
      transpose_vecMulVec, Matrix.neg_mul, neg_inj] at h
    exact h
  have hNJN : vecMulVec u (u ᵥ* J l S) * J l S * vecMulVec (u ᵥ* J l S) u = 0 := by
    rw [hNJ, Matrix.neg_mul, vecMulVec_mul_vecMulVec, dotProduct_vecMul_J_self, zero_smul, vecMulVec_zero, neg_zero]
  calc (1 + vecMulVec u (u ᵥ* J l S)) * J l S * (1 + vecMulVec (u ᵥ* J l S) u)
      = J l S + vecMulVec u (u ᵥ* J l S) * J l S + J l S * vecMulVec (u ᵥ* J l S) u +
          vecMulVec u (u ᵥ* J l S) * J l S * vecMulVec (u ᵥ* J l S) u := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
          Matrix.mul_assoc]
        abel
    _ = J l S := by rw [hNJN, hNJ, hJN]; abel

theorem transvection_mulVec (u w : l ⊕ l → S) :
    transvection u *ᵥ w = w + ((u ᵥ* J l S) ⬝ᵥ w) • u := by
  rw [transvection, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

end Ring

section Field

variable {F : Type*} [Field F]

/-- Given square matrices `A` and `C` over a field, if the only vector annihilated by both of
them is `0`, and `Aᵀ * C = Cᵀ * A`, then there is a symmetric matrix `X` such that `A + X * C`
is invertible. This is a verbatim copy of the private Mathlib lemma
`SymplecticGroup.exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot`
(`Mathlib/LinearAlgebra/SymplecticGroup.lean`). -/
theorem exists_isSymm_isUnit_add_mul {A C : Matrix l l F}
    (hker : ∀ (x : l → F), (A • x = 0) → (C • x = 0) → x = 0)
    (hsymm : Aᵀ * C = Cᵀ * A) :
    ∃ (X : Matrix l l F), X.IsSymm ∧ IsUnit (A + X * C) := by
  -- `C` is transformed into `P = fromBlocks 1 0 0 0` by invertible matrices `V` and `U`.
  rcases exists_rank_normal_form C with ⟨V, U, s, hV, hU, heq⟩
  set P := V * C * U with P_def; set Q := Vᵀ⁻¹ * A * U with Q_def
  set f := fun (x : Matrix l l F) ↦ x.submatrix s.symm s.symm
  have hf (x) : f x = x.submatrix s.symm s.symm := rfl
  have f_unit {x} : IsUnit x → IsUnit (f x) := (isUnit_submatrix_equiv ..).2
  have f_mul (x y) : f (x * y) = f x * f y := submatrix_mul _ _ _ _ _ s.symm.bijective
  have _ : Invertible V := hV.invertible
  have _ : Invertible U := hU.invertible
  have _ : Invertible (f Vᵀ) := (f_unit (V.isUnit_transpose.2 hV)).invertible
  -- The hypothesis that the only vector annihilated by both matrices is 0, holds for `P` and `Q`.
  have con1 (x : Fin C.rank ⊕ Fin (Fintype.card l - C.rank) → F)
      (heq1 : (f Q) • x = 0) (heq2 : (f P) • x = 0) : x = 0 := by
    refine (f_unit hU).smul_left_cancel.1 ?_
    rw [f_mul, f_mul, mul_assoc, mul_smul, IsUnit.smul_eq_zero, mul_smul, hf,
      smul_eq_mulVec, submatrix_mulVec_equiv, Equiv.symm_symm] at heq1 heq2
    · rw [Equiv.comp_symm_eq, Pi.zero_comp] at heq1 heq2
      exact s.surjective.injective_comp_right <| by simpa using hker _ heq1 heq2
    · exact f_unit hV
    · exact f_unit <| isUnit_nonsing_inv_iff.2 <| V.isUnit_transpose.2 hV
  -- The symmetry relation also holds for `P` and `Q`.
  have con2 : Qᵀ * P = Pᵀ * Q := by
    simp only [P_def, mul_assoc, transpose_mul, transpose_nonsing_inv, transpose_transpose, Q_def,
      inv_mul_cancel_left_of_invertible, mul_inv_cancel_left_of_invertible]
    rw [← mul_assoc Aᵀ, hsymm, mul_assoc]
  replace con2 : (f Q).toBlocks₁₁ᵀ = (f Q).toBlocks₁₁ ∧ (f Q).toBlocks₁₂ = 0 := by
    apply_fun reindex s s at con2
    rw [reindex_apply, reindex_apply, ← hf, ← hf, f_mul, f_mul Pᵀ, heq, hf,
      ← transpose_submatrix, ← hf Q, ← (f Q).fromBlocks_toBlocks, hf (_)ᵀ, hf
      ((fromBlocks 1 0 0 0).submatrix _ _)] at con2
    simp [fromBlocks_transpose, fromBlocks_multiply] at con2; tauto
  -- The lower-right block of `Q` is invertible.
  have con3 : IsUnit (f Q).toBlocks₂₂ := by
    refine mulVec_injective_iff_isUnit.1 ?_
    rw [← coe_mulVecLin, ← LinearMap.ker_eq_bot]
    refine ker_mulVecLin_eq_bot_iff.2 fun x hx ↦ Sum.elim_injective' <|
      (con1 _ ?_ ?_).trans Sum.elim_zero_zero.symm
    · rw [← (f Q).fromBlocks_toBlocks]; simp [hx, con2.2, fromBlocks_mulVec]
    · simp [hf, heq, fromBlocks_mulVec]
  set Y : Matrix (Fin C.rank ⊕ Fin (Fintype.card l - C.rank)) (Fin C.rank ⊕
    Fin (Fintype.card l - C.rank)) F := fromBlocks (1 - (f Q).toBlocks₁₁) 0 0 0 with Y_def
  have hY_symm : Y.IsSymm := by
    rw [Y_def, isSymm_fromBlocks_iff]
    exact ⟨IsSymm.sub isSymm_one con2.1, by simp⟩
  -- We now take `X = Vᵀ * Y * V` and this gives the desired matrix `X.submatrix s s`.
  set X := (f Vᵀ) * Y * (f V) with X_def
  refine ⟨X.submatrix s s, IsSymm.submatrix ?_ s, (isUnit_submatrix_equiv s.symm s.symm).1 ?_⟩
  · simp_rw [X_def, Matrix.IsSymm, transpose_mul, hY_symm.eq, hf, transpose_submatrix,
      transpose_transpose, mul_assoc]
  · have heq' : f (A + X.submatrix s s * C) = (f Vᵀ) * (f Q + Y * (f P)) * f (U⁻¹) := by
      simp_rw [hf, submatrix_add, Pi.add_apply, Q_def, P_def, ← hf, f_mul, hf, mul_add, ← mul_assoc,
        ← inv_submatrix_equiv, add_mul, mul_assoc _ (U.submatrix _ _), mul_inv_of_invertible]
      simp [X_def]; rfl
    rw [← hf, heq', IsUnit.mul_iff, IsUnit.mul_iff]
    refine ⟨⟨isUnit_of_invertible _, ?_⟩, ?_⟩
    · nth_rw 1 [Y_def, heq, ← (f Q).fromBlocks_toBlocks, con2.2]
      simpa [hf, fromBlocks_multiply, fromBlocks_add]
    · exact f_unit <| isUnit_nonsing_inv_iff.2 hU

/-- A symplectic matrix with invertible upper-left block `a` is
`lower (C a⁻¹) * levi a * upper (a⁻¹ B)`. -/
theorem fromBlocks_eq_lower_mul_levi_mul_upper (a : GL l F) {B C D : Matrix l l F}
    (hM : fromBlocks (a : Matrix l l F) B C D ∈ symplecticGroup l F) :
    (C * ((a⁻¹ : GL l F) : Matrix l l F)).IsSymm ∧
      fromBlocks (a : Matrix l l F) B C D =
        lower (C * ((a⁻¹ : GL l F) : Matrix l l F)) * levi a *
          upper (((a⁻¹ : GL l F) : Matrix l l F) * B) := by
  obtain ⟨h1, -, h3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 hM
  set A := (a : Matrix l l F)
  set A' := ((a⁻¹ : GL l F) : Matrix l l F)
  have hAA' : A * A' = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hA'A : A' * A = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hZ : (C * A')ᵀ = C * A' := by
    rw [transpose_mul]
    calc A'ᵀ * Cᵀ = A'ᵀ * Cᵀ * (A * A') := by rw [hAA', Matrix.mul_one]
      _ = A'ᵀ * (Cᵀ * A) * A' := by simp only [Matrix.mul_assoc]
      _ = A'ᵀ * (Aᵀ * C) * A' := by rw [h1]
      _ = (A * A')ᵀ * C * A' := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = C * A' := by rw [hAA', transpose_one, Matrix.one_mul]
  have hD : C * A' * B + A'ᵀ = D := by
    have h : A'ᵀ * (Aᵀ * D - Cᵀ * B) = A'ᵀ := by rw [h3, Matrix.mul_one]
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul,
      ← transpose_mul, hAA', transpose_one, Matrix.one_mul, hZ] at h
    rw [← h]
    abel
  refine ⟨hZ, ?_⟩
  simp only [lower, levi, upper, fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [fromBlocks_inj]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, hAA', Matrix.one_mul]
  · rw [Matrix.mul_assoc, hA'A, Matrix.mul_one]
  · rw [Matrix.mul_assoc C A' A, hA'A, Matrix.mul_one, ← Matrix.mul_assoc, hD]

/-- **Big-cell decomposition.** Over a field, every symplectic matrix is a product
`upper X * lower Z * levi A * upper Y` with `X`, `Z`, `Y` symmetric. -/
theorem exists_eq_upper_mul_lower_mul_levi_mul_upper {M : Matrix (l ⊕ l) (l ⊕ l) F}
    (hM : M ∈ symplecticGroup l F) :
    ∃ X Z Y : Matrix l l F, X.IsSymm ∧ Z.IsSymm ∧ Y.IsSymm ∧ ∃ A : GL l F,
      M = upper X * lower Z * levi A * upper Y := by
  set A := M.toBlocks₁₁
  set B := M.toBlocks₁₂
  set C := M.toBlocks₂₁
  set D := M.toBlocks₂₂
  have hM' : fromBlocks A B C D ∈ symplecticGroup l F := by
    rw [fromBlocks_toBlocks]
    exact hM
  have hunit : IsUnit M :=
    (isUnit_iff_isUnit_det M).2 (by rw [SymplecticGroup.det_eq_one hM]; exact isUnit_one)
  have hker : ∀ x : l → F, A • x = 0 → C • x = 0 → x = 0 := by
    intro x h1 h2
    have h : M *ᵥ Sum.elim x 0 = M *ᵥ Sum.elim 0 0 := by
      rw [← fromBlocks_toBlocks M, fromBlocks_mulVec, fromBlocks_mulVec]
      rw [smul_eq_mulVec] at h1 h2
      simp [h1, h2, A, C]
    exact (Sum.elim_eq_iff.1 (mulVec_injective_iff_isUnit.2 hunit h)).1
  obtain ⟨X, hX, hXunit⟩ :=
    exists_isSymm_isUnit_add_mul hker (SymplecticGroup.fromBlocks_mem_iff.1 hM').1
  let a : GL l F := hXunit.unit
  have ha : (a : Matrix l l F) = A + X * C := hXunit.unit_spec
  have hXM : upper X * M = fromBlocks (a : Matrix l l F) (B + X * D) C D := by
    rw [ha, ← fromBlocks_toBlocks M, upper, fromBlocks_multiply]
    simp [A, B, C, D]
  have hM'' : fromBlocks (a : Matrix l l F) (B + X * D) C D ∈ symplecticGroup l F := by
    rw [← hXM]
    exact Submonoid.mul_mem _ (upper_mem hX) hM
  obtain ⟨hZ, hfac⟩ := fromBlocks_eq_lower_mul_levi_mul_upper a hM''
  set Z := C * ((a⁻¹ : GL l F) : Matrix l l F)
  set Y := ((a⁻¹ : GL l F) : Matrix l l F) * (B + X * D)
  have hY : Y.IsSymm := by
    have hmem : upper Y ∈ symplecticGroup l F := by
      let P : symplecticGroup l F :=
        ⟨lower Z * levi a, Submonoid.mul_mem _ (lower_mem hZ) (levi_mem a)⟩
      let Q : symplecticGroup l F := ⟨_, hM''⟩
      have h : ((P⁻¹ * Q : symplecticGroup l F) : Matrix (l ⊕ l) (l ⊕ l) F) = upper Y := by
        rw [Submonoid.coe_mul]
        change ((P⁻¹ : symplecticGroup l F) : Matrix (l ⊕ l) (l ⊕ l) F) *
          fromBlocks (a : Matrix l l F) (B + X * D) C D = _
        rw [hfac, ← Matrix.mul_assoc]
        change ((P⁻¹ * P : symplecticGroup l F) : Matrix (l ⊕ l) (l ⊕ l) F) * _ = _
        rw [inv_mul_cancel, Submonoid.coe_one, Matrix.one_mul]
      rw [← h]
      exact (P⁻¹ * Q).2
    have h := (SymplecticGroup.fromBlocks_mem_iff.1 hmem).2.1
    have h' : Yᵀ = Y := by simpa using h
    exact h'
  refine ⟨-X, Z, Y, hX.neg, hZ, hY, a, ?_⟩
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (lower Z), ← hfac, ← hXM,
    ← Matrix.mul_assoc, upper_mul_upper, neg_add_cancel, upper_zero, Matrix.one_mul]

/-- **Irreducibility.** A nonzero subspace of the column space stable under all symplectic
matrices over a field is the whole space. -/
theorem eq_top_of_forall_mulVec_mem (W : Submodule F (l ⊕ l → F))
    (hW : ∀ g ∈ symplecticGroup l F, ∀ w ∈ W, g *ᵥ w ∈ W) (h0 : W ≠ ⊥) : W = ⊤ := by
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have key : ∀ u : l ⊕ l → F, (u ᵥ* J l F) ⬝ᵥ w ≠ 0 → u ∈ W := by
    intro u hu
    have h := W.sub_mem (hW _ (transvection_mem u) w hwW) hwW
    rw [transvection_mulVec, add_sub_cancel_left] at h
    have h' := W.smul_mem ((u ᵥ* J l F) ⬝ᵥ w)⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ hu, one_smul] at h'
  have hJw : J l F *ᵥ w ≠ 0 := by
    intro h
    apply hw0
    have h' := congrArg (fun v => J l F *ᵥ v) h
    simp only [mulVec_mulVec, J_squared, mulVec_zero, neg_mulVec, one_mulVec, neg_eq_zero] at h'
    exact h'
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hJw
  set u₀ : l ⊕ l → F := Pi.single k 1
  have hu₀ : (u₀ ᵥ* J l F) ⬝ᵥ w ≠ 0 := by
    rw [← dotProduct_mulVec, single_dotProduct, one_mul]
    exact hk
  rw [eq_top_iff]
  intro u _
  by_cases hu : (u ᵥ* J l F) ⬝ᵥ w = 0
  · have h : (u + u₀) ∈ W := key _ (by rwa [add_vecMul, add_dotProduct, hu, zero_add])
    have h' := W.sub_mem h (key u₀ hu₀)
    rwa [add_sub_cancel_right] at h'
  · exact key u hu

end Field

end Langlands.GroupScheme.SymplecticMatrix
