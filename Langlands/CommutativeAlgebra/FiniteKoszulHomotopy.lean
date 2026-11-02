import Langlands.CommutativeAlgebra.FiniteKoszulComplex

/-! # Generator homotopies for the finite subset Koszul differential -/

universe u v

namespace Langlands.CommutativeAlgebra

open scoped BigOperators

variable {R : Type u} [CommRing R]
variable {ι : Type v} [LinearOrder ι]

/-- Exterior multiplication by the generator indexed by `j`, in subset coordinates. -/
noncomputable def koszulAmbientInsertion (j : ι) :
    (Finset ι → R) →ₗ[R] (Finset ι → R) where
  toFun x s := if j ∈ s then koszulSign R s j * x (s.erase j) else 0
  map_add' x y := by
    ext s
    by_cases hj : j ∈ s <;> simp [hj, mul_add]
  map_smul' r x := by
    ext s
    by_cases hj : j ∈ s <;> simp [hj, mul_left_comm]

private lemma sign_insert_same (s : Finset ι) (i : ι) :
    koszulSign R (insert i s) i = koszulSign R s i :=
  koszulSign_insert_of_not_lt s (lt_irrefl i)

private lemma sign_erase_same (s : Finset ι) (i : ι) :
    koszulSign R (s.erase i) i = koszulSign R s i := by
  by_cases hi : i ∈ s
  · simpa only [Finset.insert_erase hi] using (sign_insert_same (R := R) (s.erase i) i).symm
  · rw [Finset.erase_eq_of_notMem hi]

private lemma sign_insertion_cancel (s : Finset ι) (i j : ι)
    (hi : i ∉ s) (hj : j ∈ s) :
    koszulSign R s i * koszulSign R (insert i s) j +
      koszulSign R s j * koszulSign R (s.erase j) i = 0 := by
  have hij : i ≠ j := fun h ↦ hi (h ▸ hj)
  have hi' : i ∉ s.erase j := fun h ↦ hi (Finset.mem_of_mem_erase h)
  have hs : insert j (s.erase j) = s := Finset.insert_erase hj
  rw [← hs]
  rw [Finset.insert_comm i j, sign_insert_same]
  simp only [Finset.erase_insert, Finset.notMem_erase, not_false_eq_true,
    sign_insert_same]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · rw [koszulSign_insert_of_not_lt _ (not_lt_of_gt hlt),
      koszulSign_insert_of_lt _ hi' hlt]
    ring
  · rw [koszulSign_insert_of_lt _ (Finset.notMem_erase _ _) hgt,
      koszulSign_insert_of_not_lt _ (not_lt_of_gt hgt)]
    ring

variable [Fintype ι]

/-- Insertion contracts multiplication by one of the Koszul parameters. -/
theorem koszulAmbientInsertion_identity (a : ι → R) (j : ι) :
    (koszulAmbientDifferential a).comp (koszulAmbientInsertion j) +
      (koszulAmbientInsertion j).comp (koszulAmbientDifferential a) =
        a j • LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext s
  change (∑ i, koszulCoefficient a s i *
      (if j ∈ insert i s then koszulSign R (insert i s) j *
        x ((insert i s).erase j) else 0)) +
    (if j ∈ s then koszulSign R s j *
      (∑ i, koszulCoefficient a (s.erase j) i * x (insert i (s.erase j))) else 0) =
        a j * x s
  by_cases hj : j ∈ s
  · simp only [hj, ↓reduceIte]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [Finset.sum_eq_single j]
    · simp [koszulCoefficient, hj, sign_erase_same, koszulSign_mul_self, ← mul_assoc]
    · intro i _ hij
      by_cases hi : i ∈ s
      · have hi' : i ∈ s.erase j := Finset.mem_erase.mpr ⟨hij, hi⟩
        simp [koszulCoefficient, hi, hi']
      · have hi' : i ∉ s.erase j := fun h ↦ hi (Finset.mem_of_mem_erase h)
        have he : (insert i s).erase j = insert i (s.erase j) :=
          Finset.erase_insert_of_ne hij
        simp only [koszulCoefficient, hi, hi', ↓reduceIte,
          Finset.mem_insert_of_mem hj, he]
        have hsign := sign_insertion_cancel (R := R) s i j hi hj
        linear_combination a i * x (insert i (s.erase j)) * hsign
    · simp
  · simp only [hj, ↓reduceIte]
    rw [add_zero, Finset.sum_eq_single j]
    · simp only [koszulCoefficient, hj, ↓reduceIte, Finset.mem_insert_self,
        sign_insert_same, Finset.erase_insert hj]
      linear_combination a j * x s * (koszulSign_mul_self (R := R) s j)
    · intro i _ hij
      simp [Finset.mem_insert, hj, Ne.symm hij]
    · simp

/-- Exterior insertion between adjacent homogeneous Koszul degrees. -/
noncomputable def finiteKoszulInsertion (j : ι) (n : ℕ) :
    FiniteKoszulModule R ι n →ₗ[R] FiniteKoszulModule R ι (n + 1) :=
  (koszulRestrict (n + 1)).comp ((koszulAmbientInsertion j).comp (koszulExtend n))

omit [Fintype ι] in
lemma koszulExtend_insertion (j : ι) (n : ℕ) (x : FiniteKoszulModule R ι n) :
    koszulExtend (n + 1) (finiteKoszulInsertion j n x) =
      koszulAmbientInsertion j (koszulExtend n x) := by
  funext s
  by_cases hs : s.card = n + 1
  · simp [koszulExtend, finiteKoszulInsertion, koszulRestrict, hs]
  · simp only [koszulExtend, LinearMap.coe_mk, AddHom.coe_mk, hs, ↓reduceDIte]
    symm
    by_cases hj : j ∈ s
    · have hcard : (s.erase j).card ≠ n := by
        rw [Finset.card_erase_of_mem hj]
        have := Finset.card_pos.mpr ⟨j, hj⟩
        omega
      simp only [koszulAmbientInsertion, LinearMap.coe_mk, AddHom.coe_mk,
        hj, ↓reduceIte, hcard, ↓reduceDIte, mul_zero]
    · simp [koszulAmbientInsertion, hj]

lemma koszulAmbientDifferential_extend_zero (a : ι → R)
    (x : FiniteKoszulModule R ι 0) :
    koszulAmbientDifferential a (koszulExtend 0 x) = 0 := by
  funext s
  change (∑ i, koszulCoefficient a s i * koszulExtend 0 x (insert i s)) = 0
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ s
  · simp [koszulCoefficient, hi]
  · simp [koszulExtend]

/-- The insertion identity in a positive homogeneous degree. -/
theorem finiteKoszulInsertion_identity (a : ι → R) (j : ι) (n : ℕ) :
    (finiteKoszulDifferential a (n + 1)).comp (finiteKoszulInsertion j (n + 1)) +
      (finiteKoszulInsertion j n).comp (finiteKoszulDifferential a n) =
        a j • LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply koszulExtend_injective (n + 1)
  change koszulExtend (n + 1)
    (finiteKoszulDifferential a (n + 1) (finiteKoszulInsertion j (n + 1) x) +
      finiteKoszulInsertion j n (finiteKoszulDifferential a n x)) =
        koszulExtend (n + 1) (a j • x)
  rw [map_add, map_smul, koszulExtend_differential, koszulExtend_insertion,
    koszulExtend_insertion, koszulExtend_differential]
  exact LinearMap.congr_fun (koszulAmbientInsertion_identity a j) (koszulExtend (n + 1) x)

/-- The insertion identity at the bottom homogeneous degree. -/
theorem finiteKoszulInsertion_identity_zero (a : ι → R) (j : ι) :
    (finiteKoszulDifferential a 0).comp (finiteKoszulInsertion j 0) =
      a j • LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply koszulExtend_injective 0
  change koszulExtend 0 (finiteKoszulDifferential a 0 (finiteKoszulInsertion j 0 x)) =
    koszulExtend 0 (a j • x)
  rw [map_smul, koszulExtend_differential, koszulExtend_insertion]
  have h := LinearMap.congr_fun (koszulAmbientInsertion_identity a j) (koszulExtend 0 x)
  simpa only [LinearMap.add_apply, LinearMap.comp_apply,
    koszulAmbientDifferential_extend_zero, map_zero, add_zero,
    LinearMap.smul_apply, LinearMap.id_apply] using h

end Langlands.CommutativeAlgebra
