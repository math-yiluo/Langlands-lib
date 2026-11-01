import Langlands.Representation.RankinSelberg.TwoBlockDominantResidualCharacter

/-! # Actual lower-group matrix factorization for the dominant rectangles -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open GeneralLinear TwoBlockLowerUnipotentQuotient

universe uF

/-- Standard consecutive two-block coordinates with a specified rank equality. -/
def splitCoordinates (a d n : ℕ) (H : a+d=n) : Fin a ⊕ Fin d ≃ Fin n :=
  finSumFinEquiv.trans (finCongr H)

/-- Reverse each of the two consecutive blocks without interchanging them. -/
def splitReflection (a d n : ℕ) (H : a+d=n) : Equiv.Perm (Fin n) :=
  (splitCoordinates a d n H).symm.trans
    ((Equiv.sumCongr Fin.revPerm Fin.revPerm).trans (splitCoordinates a d n H))

@[simp] theorem splitReflection_split (a d n : ℕ) (H : a+d=n) (i : Fin a ⊕ Fin d) :
    splitReflection a d n H (splitCoordinates a d n H i) =
      splitCoordinates a d n H ((Equiv.sumCongr Fin.revPerm Fin.revPerm) i) := by
  simp [splitReflection]

@[simp] theorem splitReflection_inv (a d n : ℕ) (H : a+d=n) :
    (splitReflection a d n H)⁻¹ = splitReflection a d n H := by
  ext i
  obtain ⟨i,rfl⟩ := (splitCoordinates a d n H).surjective i
  rcases i with i | i <;> simp [splitReflection]

variable {K : Type uF} [Field K]

/-- The block sum of unsigned Weyl matrices is the corresponding actual permutation. -/
theorem blockWeyl_permutation {t r j k : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1)) :
    blockWeyl (K := K) h hr = permutation (r+1) K
      (splitReflection (m 0+1) ((j+k+1)+(m 1+1)) (r+1) (totalRank h hr)) := by
  apply Units.ext
  ext i l
  obtain ⟨i,rfl⟩ := (splitCoordinates _ _ _ (totalRank h hr)).surjective i
  obtain ⟨l,rfl⟩ := (splitCoordinates _ _ _ (totalRank h hr)).surjective l
  rw [permutation_entry, splitReflection_split]
  change blockSum (weylLong (m 0+1) K, weylLong ((j+k+1)+(m 1+1)) K)
    (finSumFinEquiv i) (finSumFinEquiv l) = _
  rcases i with i | i <;> rcases l with l | l <;>
    simp [splitCoordinates, weylLong_entry]
  all_goals
    intro he
    have heval := congrArg Fin.val he
    simp only [Fin.val_natAdd, Fin.val_castAdd] at heval
    have hi := i.isLt
    have hl := l.rev.isLt
    omega

/-- Its row/column permutation in the five-block coordinates. -/
def reflectedIndex {t r j k : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1)) :
    Coordinates (m 0+1) j k (m 1+1) → Fin (r+1)
  | .inl i => ⟨i.rev.val, by have := TwoBlockJacquet.blockRanks_add h; have := i.rev.isLt; omega⟩
  | .inr (.inl i) => ⟨t+1+(middleCoordinates j k i).rev.val,
      by have := (middleCoordinates j k i).rev.isLt; omega⟩
  | .inr (.inr i) => ⟨(m 0+1)+i.rev.val,
      by have := TwoBlockJacquet.blockRanks_add h; have := i.rev.isLt; omega⟩

/-- Block-Weyl action sends `(a,c,b)` to the source order `(a,b,c)`, reversing internally. -/
theorem splitReflection_coordinates {t r j k : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (i : Coordinates (m 0+1) j k (m 1+1)) :
    splitReflection (m 0+1) ((j+k+1)+(m 1+1)) (r+1) (totalRank h hr)
      (coordinates h hr i) = reflectedIndex h hr i := by
  rcases i with i | (i | i)
  · apply Fin.ext
    simp [coordinates, orderedCoordinates, splitReflection, splitCoordinates, reflectedIndex]
  · apply Fin.ext
    simp [coordinates, orderedCoordinates, splitReflection, splitCoordinates, reflectedIndex,
      Fin.val_rev]
    have hc := (middleCoordinates j k i).isLt
    have := TwoBlockJacquet.blockRanks_add h
    omega
  · apply Fin.ext
    simp [coordinates, orderedCoordinates, splitReflection, splitCoordinates, reflectedIndex,
      Fin.val_rev]
    omega

/-- Entrywise action of the actual block-Weyl conjugation. -/
theorem blockWeyl_conjugate_entry {t r j k : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (g : GeneralLinear (r+1) K) (i l : Coordinates (m 0+1) j k (m 1+1)) :
    ((blockWeyl (K := K) h hr * g * blockWeyl h hr) : GeneralLinear (r+1) K) (coordinates h hr i) (coordinates h hr l) =
      g (reflectedIndex h hr i) (reflectedIndex h hr l) := by
  have he := permutation_conjugate_entry (r+1) K
    (splitReflection (m 0+1) ((j+k+1)+(m 1+1)) (r+1) (totalRank h hr))
    g (coordinates h hr i) (coordinates h hr l)
  simpa only [blockWeyl_permutation, permutation_inv, splitReflection_inv,
    splitReflection_coordinates] using he

variable {t r j k : ℕ} {m : Fin 2 → ℕ}

@[simp] theorem reflectedIndex_A_lt (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (i : Fin (m 0+1)) : (reflectedIndex h hr (.inl i)).val < t+1 := by
  have := TwoBlockJacquet.blockRanks_add h
  have := i.rev.isLt
  simp only [reflectedIndex]
  omega

@[simp] theorem reflectedIndex_B_lt (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (i : Fin (m 1+1)) : (reflectedIndex h hr (.inr (.inr i))).val < t+1 := by
  have := TwoBlockJacquet.blockRanks_add h
  have := i.rev.isLt
  simp only [reflectedIndex]
  omega

@[simp] theorem reflectedIndex_C_not_lt (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (i : Middle j k) : ¬(reflectedIndex h hr (.inr (.inl i))).val < t+1 := by
  simp only [reflectedIndex]
  omega

@[simp] theorem reflectedIndex_A_source (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (i : Fin (m 0+1)) :
    (⟨(reflectedIndex h hr (.inl i)).val, reflectedIndex_A_lt h hr i⟩ : Fin (t+1)) =
      (succBlockShape m h).index 0 i.rev := by
  apply Fin.ext
  simpa only [reflectedIndex] using (TwoBlockDeformation.val_index_zero h i.rev).symm

@[simp] theorem reflectedIndex_B_source (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (i : Fin (m 1+1)) :
    (⟨(reflectedIndex h hr (.inr (.inr i))).val, reflectedIndex_B_lt h hr i⟩ : Fin (t+1)) =
      (succBlockShape m h).index 1 i.rev := by
  apply Fin.ext
  simpa only [reflectedIndex] using (TwoBlockDeformation.val_index_one h i.rev).symm

/-- Reflection is injective even across the five source blocks. -/
theorem reflectedIndex_injective (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1)) :
    Function.Injective (reflectedIndex h hr) := by
  intro i l he
  rw [← splitReflection_coordinates, ← splitReflection_coordinates] at he
  exact (coordinates h hr).injective
    ((splitReflection _ _ _ (totalRank h hr)).injective he)

/-- The conjugated inclusion is exactly the computed three-block lower matrix. -/
theorem blockWeyl_append_lower (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (u : lowerBlockUnipotent h K) :
    blockWeyl h hr * append hr u.val * blockWeyl h hr =
      reindex (coordinates h hr)
        (BlockAlgebra.lower (C := Middle j k) (leftMultiplier h u)
          (rightMultiplier h u) (crossMultiplier h u)) := by
  apply Units.ext
  ext i l
  obtain ⟨i,rfl⟩ := (coordinates h hr).surjective i
  obtain ⟨l,rfl⟩ := (coordinates h hr).surjective l
  rw [blockWeyl_conjugate_entry]
  change append hr u.val (reflectedIndex h hr i) (reflectedIndex h hr l) =
    (BlockAlgebra.lower _ _ _).val ((coordinates h hr).symm (coordinates h hr i))
      ((coordinates h hr).symm (coordinates h hr l))
  simp only [Equiv.symm_apply_apply, BlockAlgebra.lower_val]
  rw [append_entry]
  have hinj (i l : Coordinates (m 0+1) j k (m 1+1)) :
      reflectedIndex h hr i = reflectedIndex h hr l ↔ i=l :=
    (reflectedIndex_injective h hr).eq_iff
  rcases i with i | (i | i) <;> rcases l with l | (l | l) <;>
    simp only [reflectedIndex_A_lt, reflectedIndex_B_lt, reflectedIndex_C_not_lt,
      dite_true, dite_false, reflectedIndex_A_source, reflectedIndex_B_source] <;>
    simp [BlockAlgebra.three,
      leftMultiplier_apply, rightMultiplier_apply, diagonalBlocks_apply,
      crossMultiplier_apply, index_zero_one_eq_zero h K u.property, hinj,
      Matrix.one_apply]

/-- Actual lower-group factorization with both simultaneously transformed rectangles. -/
theorem rectangle_lower_factorization
    (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (u : lowerBlockUnipotent h K)
    (x : Matrix (Fin (m 0+1)) (Fin k) K)
    (y : Matrix (Fin j) (Fin (m 1+1)) K) :
    rectangleUnipotent h hr x y * blockWeyl h hr * append hr u.val * blockWeyl h hr =
      residualMatrix h hr u x y * rectangleUnipotent h hr
        (((leftMultiplier h u)⁻¹).val * x) (y * (rightMultiplier h u).val) := by
  rw [show rectangleUnipotent h hr x y * blockWeyl h hr * append hr u.val * blockWeyl h hr =
      rectangleUnipotent h hr x y * (blockWeyl h hr * append hr u.val * blockWeyl h hr)
      by simp only [mul_assoc], blockWeyl_append_lower]
  change reindex (coordinates h hr) (BlockAlgebra.upper _ _ _) *
      reindex (coordinates h hr) (BlockAlgebra.lower _ _ _) =
    reindex (coordinates h hr) (BlockAlgebra.residual _ _ _ _ _ _) *
      reindex (coordinates h hr) (BlockAlgebra.upper _ _ _)
  rw [← map_mul, BlockAlgebra.factorization, map_mul]
  congr 1
  congr 1
  apply Units.ext
  simp only [BlockAlgebra.upper_val, mul_padX, padY_mul]

/-- Matrix covariance for the computed actual general-linear residual. -/
theorem matrix_covariance_raw
    (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (u : lowerBlockUnipotent h K) (g : GeneralLinear (t+1) K)
    (x : Matrix (Fin (m 0+1)) (Fin k) K)
    (y : Matrix (Fin j) (Fin (m 1+1)) K) :
    matrix h hr (u.val*g) x y =
      (weylLong (r+1) K * residualMatrix h hr u x y * weylLong (r+1) K) *
        matrix h hr g (((leftMultiplier h u)⁻¹).val * x) (y * (rightMultiplier h u).val) := by
  have hf := congrArg (fun z : GeneralLinear (r+1) K => z * blockWeyl h hr)
    (rectangle_lower_factorization h hr u x y)
  simp only [mul_assoc, blockWeyl_mul_self, mul_one] at hf
  unfold matrix
  rw [map_mul]
  calc
    _ = weylLong (r+1) K *
        (rectangleUnipotent h hr x y * blockWeyl h hr * append hr u.val) * append hr g := by
      simp only [mul_assoc]
    _ = weylLong (r+1) K *
        (residualMatrix h hr u x y * rectangleUnipotent h hr
          (((leftMultiplier h u)⁻¹).val * x) (y * (rightMultiplier h u).val) * blockWeyl h hr) *
        append hr g := by
          simpa only [mul_assoc] using congrArg
            (fun z : GeneralLinear (r+1) K => weylLong (r+1) K * z * append hr g) hf
    _ = _ := by simp only [mul_assoc, ← mul_assoc (weylLong (r+1) K)
      (weylLong (r+1) K), weylLong_mul_self, one_mul]

/-- The lower-group covariance uses an actual standard upper-unipotent element. -/
theorem matrix_covariance
    (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
    (u : lowerBlockUnipotent h K) (g : GeneralLinear (t+1) K)
    (x : Matrix (Fin (m 0+1)) (Fin k) K)
    (y : Matrix (Fin j) (Fin (m 1+1)) K) :
    matrix h hr (u.val*g) x y = (residualUnipotent h hr u x y).val *
      matrix h hr g ((rectangleChange h j k u (x,y)).1) ((rectangleChange h j k u (x,y)).2) := by
  exact matrix_covariance_raw h hr u g x y

end Langlands.RankinSelberg.TwoBlockDominantRectangular
