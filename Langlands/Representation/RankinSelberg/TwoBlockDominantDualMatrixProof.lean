import Langlands.Representation.RankinSelberg.TwoBlockDominantDualMatrixStatement
import Langlands.Representation.RankinSelberg.TwoBlockDominantCovarianceData

/-! # Proof of the actual reversed-dual dominant matrices -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear TwoBlockDominantRectangular TwoBlockLowerUnipotentQuotient

namespace DominantDualMatrixProof

universe uF

private theorem splitReflection_val (a d n : ℕ) (H : a+d=n) (i : Fin n) :
    (splitReflection a d n H i).val =
      if i.val < a then a-1-i.val else n+a-1-i.val := by
  obtain ⟨i,rfl⟩ := (splitCoordinates a d n H).surjective i
  rcases i with i | i <;>
    simp [splitReflection, splitCoordinates, Fin.val_rev] <;>
    have hi := i.isLt <;> omega

variable {K : Type uF} [Field K]

private theorem reindex_permutation {a b : ℕ} (e : Fin a ≃ Fin b)
    (s : Equiv.Perm (Fin a)) :
    reindex (R := K) e (permutation a K s) =
      permutation b K (e.symm.trans (s.trans e)) := by
  apply Units.ext
  ext i l
  change permutation a K s (e.symm i) (e.symm l) = _
  simp only [permutation_entry, Equiv.trans_apply]
  congr 1
  exact propext e.eq_symm_apply

private theorem blockSum_permutation {a b : ℕ}
    (s : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b)) :
    blockSum (permutation a K s, permutation b K q) =
      permutation (a+b) K
        (finSumFinEquiv.symm.trans ((Equiv.sumCongr s q).trans finSumFinEquiv)) := by
  apply Units.ext
  ext i l
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨l,rfl⟩ := finSumFinEquiv.surjective l
  simp only [permutation_entry, Equiv.trans_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases l with l | l <;>
    simp [permutation_entry]
  · intro he
    have heval := congrArg Fin.val he
    simp only [Fin.val_natAdd, Fin.val_castAdd] at heval
    have hi := i.isLt
    have hl := (q l).isLt
    omega
  · intro he
    have heval := congrArg Fin.val he
    simp only [Fin.val_natAdd, Fin.val_castAdd] at heval
    have hi := i.isLt
    have hl := (s l).isLt
    omega

private theorem splitWeyl_permutation (a d n : ℕ) (H : a+d=n) :
    reindex (finCongr H) (blockSum (weylLong a K, weylLong d K)) =
      permutation n K (splitReflection a d n H) := by
  rw [weylLong, weylLong, blockSum_permutation, reindex_permutation]
  rfl

private theorem append_blockSum {t r j k : ℕ} (hr : r=t+(j+k+1))
    (g : GeneralLinear (t+1) K) :
    append hr g =
      reindex (finCongr (by omega : (t+1)+(j+k+1)=r+1)) (blockSum (g,1)) := by
  apply Units.ext
  ext i l
  obtain ⟨i,rfl⟩ := (splitCoordinates (t+1) (j+k+1) (r+1) (by omega)).surjective i
  obtain ⟨l,rfl⟩ := (splitCoordinates (t+1) (j+k+1) (r+1) (by omega)).surjective l
  rw [append_entry]
  change _ = blockSum (g,1) (finSumFinEquiv i) (finSumFinEquiv l)
  rcases i with i | i <;> rcases l with l | l <;>
    simp [splitCoordinates, Fin.ext_iff, Matrix.one_apply]
  all_goals
    have hi := i.isLt
    have hl := l.isLt
    try intro hh
    split_ifs
  all_goals first | rfl | omega

private theorem append_weyl_right {t r j k : ℕ} (hr : r=t+(j+k+1)) :
    append (K := K) hr (weylLong (t+1) K) * rightWeyl hr =
      permutation (r+1) K
        (splitReflection (t+1) (j+k+1) (r+1) (by omega)) := by
  rw [append_blockSum, rightWeyl, ← map_mul, ← map_mul]
  simp only [Prod.mk_mul_mk, mul_one, one_mul]
  exact splitWeyl_permutation _ _ _ _

private theorem threeWeyl {t r j k : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i+1)=t+1) (hr : r=t+(j+k+1)) :
    blockWeyl (K := K) (m := fun i => m i.rev) (j := k) (k := j)
        (reverse_sum h) (by omega) *
        append hr (weylLong (t+1) K) * rightWeyl hr =
      weylLong (r+1) K * blockWeyl h hr := by
  rw [mul_assoc, append_weyl_right, blockWeyl_permutation, blockWeyl_permutation,
    weylLong, ← map_mul, ← map_mul]
  apply congrArg (permutation (r+1) K)
  apply Equiv.ext
  intro i
  apply Fin.ext
  change (splitReflection _ _ _ _ (splitReflection _ _ _ _ i)).val =
    ((splitReflection _ _ _ _ i).rev).val
  simp only [splitReflection_val, Fin.val_rev]
  have := TwoBlockJacquet.blockRanks_add h
  have := i.isLt
  simp only [show (0 : Fin 2).rev = 1 from by decide]
  split_ifs <;> omega

private def reverseCoordinates {a b j k : ℕ} :
    Coordinates a j k b → Coordinates b k j a
  | .inl i => .inr (.inr i.rev)
  | .inr (.inl (.inl i)) => .inr (.inl (.inr (.inr i.rev)))
  | .inr (.inl (.inr (.inl i))) => .inr (.inl (.inr (.inl i)))
  | .inr (.inl (.inr (.inr i))) => .inr (.inl (.inl i.rev))
  | .inr (.inr i) => .inl i.rev

private theorem coordinates_reverse {t r j k : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i+1)=t+1) (hr : r=t+(j+k+1))
    (i : Coordinates (m 0+1) j k (m 1+1)) :
    coordinates (m := fun i => m i.rev) (j := k) (k := j)
        (reverse_sum h) (by omega) (reverseCoordinates i) =
      (coordinates h hr i).rev := by
  apply Fin.ext
  simp only [coordinates_val, Fin.val_rev]
  have htotal := totalRank h hr
  rcases i with i | ((i | (i | i)) | i) <;>
    simp only [reverseCoordinates, position, Fin.val_rev,
      show (0 : Fin 2).rev = 1 from by decide,
      show (1 : Fin 2).rev = 0 from by decide] <;>
    have hi := i.isLt <;> omega

private theorem rectangleComparison {t r j k : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i+1)=t+1) (hr : r=t+(j+k+1))
    (xD : Matrix (Fin (m 1+1)) (Fin j) K)
    (yD : Matrix (Fin k) (Fin (m 0+1)) K) :
    weylLong (r+1) K *
        inverseTranspose (r+1) K
          (rectangleUnipotent (m := fun i => m i.rev) (j := k) (k := j)
            (reverse_sum h) (by omega) xD yD) *
        weylLong (r+1) K =
      rectangleUnipotent h hr (fun i l => -yD l.rev i.rev)
        (fun i l => -xD l.rev i.rev) := by
  apply Units.ext
  ext i l
  obtain ⟨i,rfl⟩ := (coordinates h hr).surjective i
  obtain ⟨l,rfl⟩ := (coordinates h hr).surjective l
  rw [weylLong_conjugate_entry, inverseTranspose_entry, rectangleUnipotent_inv,
    ← coordinates_reverse h hr i, ← coordinates_reverse h hr l,
    rectangleUnipotent_five_entry]
  erw [rectangleUnipotent_five_entry h hr]
  rcases i with i | ((i | (i | i)) | i) <;>
    rcases l with l | ((l | (l | l)) | l) <;>
      simp [reverseCoordinates, rectangleEntries, eq_comm]

private theorem inverseTranspose_reindex {a b : ℕ} (e : Fin a ≃ Fin b)
    (g : GeneralLinear a K) :
    inverseTranspose b K (reindex e g) = reindex e (inverseTranspose a K g) := by
  apply Units.ext
  rfl

private theorem inverseTranspose_blockSum {a b : ℕ}
    (g : GeneralLinear a K) (q : GeneralLinear b K) :
    inverseTranspose (a+b) K (blockSum (g,q)) =
      blockSum (inverseTranspose a K g, inverseTranspose b K q) := by
  apply Units.ext
  ext i l
  rw [inverseTranspose_entry, ← map_inv]
  change blockSum (g⁻¹,q⁻¹) l i = _
  induction i using Fin.addCases <;> induction l using Fin.addCases <;>
    simp [inverseTranspose_entry]

private theorem inverseTranspose_append {t r j k : ℕ} (hr : r=t+(j+k+1))
    (g : GeneralLinear (t+1) K) :
    inverseTranspose (r+1) K (append hr g) =
      append hr (inverseTranspose (t+1) K g) := by
  rw [append_blockSum, inverseTranspose_reindex, inverseTranspose_blockSum,
    map_one, ← append_blockSum]

private theorem inverseTranspose_blockWeyl {t r j k : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i+1)=t+1) (hr : r=t+(j+k+1)) :
    inverseTranspose (r+1) K (blockWeyl h hr) = blockWeyl h hr := by
  rw [blockWeyl_permutation, inverseTranspose_permutation]

private theorem inverseTranspose_rightWeyl {t r j k : ℕ} (hr : r=t+(j+k+1)) :
    inverseTranspose (r+1) K (rightWeyl hr) = rightWeyl hr := by
  rw [rightWeyl, inverseTranspose_reindex, inverseTranspose_blockSum,
    map_one, inverseTranspose_weylLong]

private theorem append_commutes_rightWeyl {t r j k : ℕ} (hr : r=t+(j+k+1))
    (g : GeneralLinear (t+1) K) :
    append hr g * rightWeyl hr = rightWeyl hr * append hr g := by
  rw [append_blockSum, rightWeyl, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  simp only [Prod.mk_mul_mk, mul_one, one_mul]

private theorem append_reverse {t r j k : ℕ} (hr : r=t+(j+k+1))
    (g : GeneralLinear (t+1) K) :
    append (j := k) (k := j) (by omega : r=t+(k+j+1)) g = append hr g := by
  apply Units.ext
  ext i l
  rw [append_entry, append_entry]

private theorem fullComparison {t r j k : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i+1)=t+1) (hr : r=t+(j+k+1))
    (xD : Matrix (Fin (m 1+1)) (Fin j) K)
    (yD : Matrix (Fin k) (Fin (m 0+1)) K)
    (g : GeneralLinear (t+1) K) :
    weylLong (r+1) K *
        inverseTranspose (r+1) K
          (reversedMatrix h hr (weylLong (t+1) K * inverseTranspose (t+1) K g) xD yD) =
      matrix h hr g (fun i l => -yD l.rev i.rev) (fun i l => -xD l.rev i.rev) := by
  have hu := congrArg (fun z : GeneralLinear (r+1) K => weylLong (r+1) K * z)
    (rectangleComparison h hr xD yD)
  simp only [← mul_assoc, weylLong_mul_self, one_mul] at hu
  simp only [reversedMatrix, matrix, map_mul, inverseTranspose_weylLong,
    inverseTranspose_blockWeyl, inverseTranspose_append, inverseTranspose_rightWeyl,
    inverseTranspose_involutive, append_reverse hr]
  simp only [← mul_assoc, weylLong_mul_self, one_mul]
  calc
    _ = inverseTranspose (r+1) K
          (rectangleUnipotent (m := fun i => m i.rev) (j := k) (k := j)
            (reverse_sum h) (by omega) xD yD) *
        (blockWeyl (m := fun i => m i.rev) (j := k) (k := j)
            (reverse_sum h) (by omega) *
          append hr (weylLong (t+1) K) * rightWeyl hr) * append hr g := by
            simp only [mul_assoc]
            rw [append_commutes_rightWeyl]
    _ = _ := by
      rw [threeWeyl h hr]
      simpa only [← mul_assoc] using
        congrArg (fun z : GeneralLinear (r+1) K => z * blockWeyl h hr * append hr g) hu

end DominantDualMatrixProof

/-- The three-Weyl identity and both actual signed reversed-dual matrix identities. -/
theorem twoBlockDominantDualMatrix.{uF} : TwoBlockDominantDualMatrixStatement.{uF} := by
  intro K _ t r j k m h hr
  refine ⟨DominantDualMatrixProof.threeWeyl h hr, ?_⟩
  intro xD yD
  exact ⟨DominantDualMatrixProof.rectangleComparison h hr xD yD,
    DominantDualMatrixProof.fullComparison h hr xD yD⟩

end Langlands.RankinSelberg
