import Langlands.Group.GL.BruhatNormalMatrixDirections
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Linear coordinates for the transverse Bruhat charts -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GeneralLinear

universe u

variable {F : Type u} [Field F] {n : ℕ}

local notation "M" => Matrix (Fin n) (Fin n) F

/-- The matrix space supported on the specified positions. -/
def matrixEntrySubmodule (F : Type u) [Field F] {n : ℕ} (P : Fin n → Fin n → Prop) :
    Submodule F (Matrix (Fin n) (Fin n) F) where
  carrier := {A | ∀ i j, ¬ P i j → A i j = 0}
  zero_mem' := by
    change ∀ i j, ¬ P i j → (0 : Matrix (Fin n) (Fin n) F) i j = 0
    intros
    rfl
  add_mem' ha hb := fun i j h => by
    change _ + _ = (0 : F)
    rw [ha i j h, hb i j h, add_zero]
  smul_mem' c A hA := fun i j h => by
    change c * A i j = 0
    rw [hA i j h, mul_zero]

/-- Retain the specified matrix entries and erase all others. -/
def matrixEntryProjection (P : Fin n → Fin n → Prop) :
    M →ₗ[F] matrixEntrySubmodule F P := by
  classical
  refine
    { toFun := fun A => ⟨fun i j => if P i j then A i j else 0, fun i j h => by
        dsimp
        simp [h]⟩
      map_add' := ?_
      map_smul' := ?_ }
  · intro A B
    apply Subtype.ext
    ext i j
    by_cases h : P i j <;> simp [h]
  · intro c A
    apply Subtype.ext
    ext i j
    by_cases h : P i j <;> simp [h]

theorem matrixEntryProjection_apply_of_pos {P : Fin n → Fin n → Prop} {i j : Fin n}
    (A : M) (h : P i j) : (matrixEntryProjection P A).val i j = A i j := by
  classical
  simp [matrixEntryProjection, h]

theorem matrixEntryProjection_apply_of_neg {P : Fin n → Fin n → Prop} {i j : Fin n}
    (A : M) (h : ¬ P i j) : (matrixEntryProjection P A).val i j = 0 :=
  (matrixEntryProjection P A).property i j h

private theorem matrixEntryProjection_self (P : Fin n → Fin n → Prop) (X : matrixEntrySubmodule F P) :
    matrixEntryProjection P X.val = X := by
  apply Subtype.ext
  ext i j
  by_cases h : P i j
  · exact matrixEntryProjection_apply_of_pos _ h
  · rw [matrixEntryProjection_apply_of_neg _ h, X.property i j h]

private theorem matrixEntryProjection_eq_zero_of_disjoint {P Q : Fin n → Fin n → Prop}
    (hPQ : ∀ i j, P i j → ¬ Q i j) (X : matrixEntrySubmodule F Q) :
    matrixEntryProjection P X.val = 0 := by
  apply Subtype.ext
  ext i j
  change (matrixEntryProjection P X.val).val i j = 0
  by_cases h : P i j
  · rw [matrixEntryProjection_apply_of_pos _ h, X.property i j (hPQ _ _ h)]
  · exact matrixEntryProjection_apply_of_neg _ h

/-- The upper triangular directions. -/
abbrev bruhatUpperSpace (F : Type u) [Field F] (n : ℕ) :=
  matrixEntrySubmodule F (fun i j : Fin n => i ≤ j)

/-- Lower triangular directions from the inversions of the inverse permutation. -/
abbrev bruhatInversionSpace (F : Type u) [Field F] {n : ℕ} (w : Equiv.Perm (Fin n)) :=
  matrixEntrySubmodule F (fun i j => j < i ∧ w.symm i < w.symm j)

/-- The complementary lower triangular directions. -/
abbrev bruhatNormalSpace (F : Type u) [Field F] {n : ℕ} (w : Equiv.Perm (Fin n)) :=
  matrixEntrySubmodule F (bruhatNormalEntry w)

private theorem bruhatUpper_disjoint_lower {i j : Fin n} (h : i ≤ j) : ¬ j < i := not_lt_of_ge h

/-- The three disjoint matrix patterns give all matrix directions. -/
def bruhatMatrixCoordinates (w : Equiv.Perm (Fin n)) :
    ((bruhatUpperSpace F n × bruhatInversionSpace F w) × bruhatNormalSpace F w) ≃ₗ[F] M where
  toFun z := z.1.1.val + z.1.2.val + z.2.val
  invFun A := ((matrixEntryProjection (fun i j => i ≤ j) A,
    matrixEntryProjection (fun i j => j < i ∧ w.symm i < w.symm j) A),
    matrixEntryProjection (bruhatNormalEntry w) A)
  left_inv := by
    rintro ⟨⟨A, B⟩, C⟩
    have huB := matrixEntryProjection_eq_zero_of_disjoint
      (fun _ _ (h : _ ≤ _) (k : _ < _ ∧ _) => bruhatUpper_disjoint_lower h k.1) B
    have huC := matrixEntryProjection_eq_zero_of_disjoint
      (fun _ _ (h : _ ≤ _) (k : bruhatNormalEntry w _ _) => bruhatUpper_disjoint_lower h k.1) C
    have hbA := matrixEntryProjection_eq_zero_of_disjoint
      (fun i j (h : j < i ∧ w.symm i < w.symm j) k => bruhatUpper_disjoint_lower k h.1) A
    have hbC := matrixEntryProjection_eq_zero_of_disjoint
      (fun i j (h : j < i ∧ w.symm i < w.symm j) (k : bruhatNormalEntry w i j) =>
        (not_lt_of_ge k.2.le) h.2) C
    have hcA := matrixEntryProjection_eq_zero_of_disjoint
      (fun _ _ (h : bruhatNormalEntry w _ _) k => bruhatUpper_disjoint_lower k h.1) A
    have hcB := matrixEntryProjection_eq_zero_of_disjoint
      (fun _ _ (h : bruhatNormalEntry w _ _) k => (not_lt_of_ge h.2.le) k.2) B
    apply Prod.ext
    · apply Prod.ext
      · simp only [map_add, matrixEntryProjection_self, huB, huC, add_zero]
      · simp only [map_add, matrixEntryProjection_self, hbA, hbC, zero_add, add_zero]
    · simp only [map_add, matrixEntryProjection_self, hcA, hcB, zero_add]
  right_inv A := by
    ext i j
    simp only [Matrix.add_apply]
    by_cases h : i ≤ j
    · rw [matrixEntryProjection_apply_of_pos _ h,
        matrixEntryProjection_apply_of_neg _ (fun g => bruhatUpper_disjoint_lower h g.1),
        matrixEntryProjection_apply_of_neg _ (fun g : bruhatNormalEntry w i j =>
          bruhatUpper_disjoint_lower h g.1), add_zero, add_zero]
    · rw [matrixEntryProjection_apply_of_neg _ h, zero_add]
      have hij : j < i := lt_of_not_ge h
      rcases lt_or_gt_of_ne ((w.symm.injective.ne hij.ne.symm)) with h₁ | h₂
      · rw [matrixEntryProjection_apply_of_pos _ ⟨hij, h₁⟩,
          matrixEntryProjection_apply_of_neg _ (fun g : bruhatNormalEntry w i j =>
            (not_lt_of_ge h₁.le) g.2), add_zero]
      · rw [matrixEntryProjection_apply_of_neg _ (fun g => (not_lt_of_ge h₂.le) g.2),
          matrixEntryProjection_apply_of_pos _ (show bruhatNormalEntry w i j from ⟨hij, h₂⟩),
          zero_add]
  map_add' z z' := by
    change (_ + _) + (_ + _) + (_ + _) = _
    abel
  map_smul' c z := by
    change c • z.1.1.val + c • z.1.2.val + c • z.2.val = _
    simp only [smul_add, RingHom.id_apply]

private def conjugatedBruhatDirections (w : Equiv.Perm (Fin n))
    (b : upperTriangularSubgroup n F) :
    (bruhatUpperSpace F n × bruhatInversionSpace F w) × bruhatNormalSpace F w →ₗ[F] M where
  toFun z := (b⁻¹ : upperTriangularSubgroup n F).val.val * z.2.val * b.val.val +
    z.1.1.val + z.1.2.val
  map_add' z z' := by
    change _ * (_ + _) * _ + (_ + _) + (_ + _) = _
    rw [mul_add, add_mul]
    abel
  map_smul' r z := by
    change _ * (r • z.2.val) * _ + r • z.1.1.val + r • z.1.2.val = _
    simp only [mul_smul_comm, smul_mul_assoc, smul_add, RingHom.id_apply]

/-- After conjugating the normal directions by the inverse upper
factor, the three Bruhat coordinate families still give all matrices. -/
def bruhatConjugatedMatrixCoordinates (w : Equiv.Perm (Fin n))
    (b : upperTriangularSubgroup n F) :
    ((bruhatUpperSpace F n × bruhatInversionSpace F w) × bruhatNormalSpace F w) ≃ₗ[F] M := by
  let e := bruhatMatrixCoordinates (F := F) w
  refine (conjugatedBruhatDirections w b).linearEquivOfInjective ?_ e.finrank_eq
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro z hz
  rw [LinearMap.mem_ker] at hz
  rcases z with ⟨⟨U, R⟩, L⟩
  change (b⁻¹ : upperTriangularSubgroup n F).val.val * L.val * b.val.val + U.val + R.val = 0 at hz
  let P : M →ₗ[F] bruhatNormalSpace F w := matrixEntryProjection (bruhatNormalEntry w)
  have hU : P U.val = 0 := matrixEntryProjection_eq_zero_of_disjoint
    (fun _ _ (h : bruhatNormalEntry w _ _) k => bruhatUpper_disjoint_lower k h.1) U
  have hR : P R.val = 0 := matrixEntryProjection_eq_zero_of_disjoint
    (fun _ _ (h : bruhatNormalEntry w _ _) k => (not_lt_of_ge h.2.le) k.2) R
  have hp := congrArg P hz
  simp only [map_add, hU, hR, add_zero, map_zero] at hp
  have hL : L = 0 := by
    apply Subtype.ext
    change L.val = 0
    apply eq_zero_of_upperConjugation_normalEntries w b L.val L.property
    intro i j h
    have he := congrArg (fun l : bruhatNormalSpace F w => l.val i j) hp
    exact (matrixEntryProjection_apply_of_pos _ h).symm.trans he
  rw [hL] at hz
  have hm : U.val + R.val = 0 := by simpa using hz
  have he : e ((U, R), 0) = e 0 := by
    rw [map_zero]
    change U.val + R.val + 0 = 0
    simpa only [add_zero] using hm
  have hd := e.injective he
  have hf := congrArg Prod.fst hd
  rw [Submodule.mem_bot]
  exact Prod.ext hf hL

@[simp]
theorem bruhatConjugatedMatrixCoordinates_apply (w : Equiv.Perm (Fin n))
    (b : upperTriangularSubgroup n F)
    (z : (bruhatUpperSpace F n × bruhatInversionSpace F w) × bruhatNormalSpace F w) :
    bruhatConjugatedMatrixCoordinates w b z =
      (b⁻¹ : upperTriangularSubgroup n F).val.val * z.2.val * b.val.val + z.1.1.val + z.1.2.val :=
  rfl

/-- Vanishing of the normal entries places a matrix in the sum of
the two Bruhat tangent spaces. -/
theorem exists_bruhatTangentCoordinates (w : Equiv.Perm (Fin n)) (A : M)
    (hA : ∀ i j, bruhatNormalEntry w i j → A i j = 0) :
    ∃ z : bruhatUpperSpace F n × bruhatInversionSpace F w, A = z.1.val + z.2.val := by
  let e := bruhatMatrixCoordinates (F := F) w
  let z := e.symm A
  have hn : z.2 = 0 := by
    apply Subtype.ext
    ext i j
    change (matrixEntryProjection (bruhatNormalEntry w) A).val i j = 0
    by_cases hij : bruhatNormalEntry w i j
    · rw [matrixEntryProjection_apply_of_pos _ hij, hA i j hij]
    · exact matrixEntryProjection_apply_of_neg A hij
  have he := e.apply_symm_apply A
  change z.1.1.val + z.1.2.val + z.2.val = A at he
  rw [hn, Submodule.coe_zero, add_zero] at he
  exact ⟨z.1, he.symm⟩

/-- An upper triangular field stays in the tangent entry patterns
after conjugation by an upper triangular unit. -/
theorem upperConjugation_normalEntry_eq_zero_of_upperTriangular
    (w : Equiv.Perm (Fin n)) (b : upperTriangularSubgroup n F) (A : M)
    (hA : A.IsUpperTriangular) {i j : Fin n} (hn : bruhatNormalEntry w i j) :
    ((b⁻¹ : upperTriangularSubgroup n F).val.val * A * b.val.val) i j = 0 :=
  ((((b⁻¹ : upperTriangularSubgroup n F).property).mul hA).mul b.property) hn.1

end Langlands.GeneralLinear
