import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Parabolic.RefinementComposition

/-! Full determinant-product modulus calculation for ordered block refinements. -/

noncomputable section

open scoped BigOperators NNReal

namespace Langlands.Parabolic.FlattenedModulusCalculation

private theorem rectangularProduct {M : Type*} [CommGroup M]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → M) (b : κ → M) (d : ι → ℕ) (e : κ → ℕ) :
    (∏ i, ∏ j, a i ^ e j / b j ^ d i) =
      (∏ i, a i) ^ (∑ j, e j) / (∏ j, b j) ^ (∑ i, d i) := by
  simp only [Finset.prod_div_distrib]
  congr 1
  · simp_rw [Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_pow _ _ _
  · rw [Finset.prod_comm]
    simp_rw [Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_pow _ _ _

private theorem lexFactor {M : Type*} [CommGroup M]
    {r : ℕ} {s : Fin r → ℕ} (a : (i : Fin r) → Fin (s i) → M)
    (d : (i : Fin r) → Fin (s i) → ℕ)
    (i k : Fin r) (j : Fin (s i)) (l : Fin (s k)) :
    (if i < k ∨ (i = k ∧ j.val < l.val) then
      a i j ^ d k l / a k l ^ d i j else 1) =
    (if i < k then a i j ^ d k l / a k l ^ d i j else 1) *
      (if i = k ∧ j.val < l.val then
        a i j ^ d k l / a k l ^ d i j else 1) := by
  classical
  by_cases h : i < k
  · simp [h, ne_of_lt h]
  · simp [h]

private theorem sameOuterProduct {M : Type*} [CommGroup M]
    {r : ℕ} {s : Fin r → ℕ} (a : (i : Fin r) → Fin (s i) → M)
    (d : (i : Fin r) → Fin (s i) → ℕ) (i : Fin r) (j : Fin (s i)) :
    (∏ k, ∏ l : Fin (s k),
      if i = k ∧ j.val < l.val then
        a i j ^ d k l / a k l ^ d i j else 1) =
      ∏ l : Fin (s i), if j < l then
        a i j ^ d i l / a i l ^ d i j else 1 := by
  classical
  rw [Finset.prod_eq_single i]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

private theorem differentOuterProduct {M : Type*} [CommGroup M]
    {r : ℕ} {s : Fin r → ℕ} (a : (i : Fin r) → Fin (s i) → M)
    (d : (i : Fin r) → Fin (s i) → ℕ) (i k : Fin r) :
    (∏ j : Fin (s i), ∏ l : Fin (s k),
      if i < k then a i j ^ d k l / a k l ^ d i j else 1) =
      if i < k then
        (∏ j, a i j) ^ (∑ l, d k l) / (∏ l, a k l) ^ (∑ j, d i j)
      else 1 := by
  classical
  split_ifs with h
  · exact rectangularProduct _ _ _ _
  · simp

private theorem lexProduct {M : Type*} [CommGroup M]
    {r : ℕ} {s : Fin r → ℕ} (a : (i : Fin r) → Fin (s i) → M)
    (d : (i : Fin r) → Fin (s i) → ℕ) :
    (∏ i, ∏ j, ∏ k, ∏ l,
      if i < k ∨ (i = k ∧ j.val < l.val) then
        a i j ^ d k l / a k l ^ d i j else 1) =
      (∏ i, ∏ k, if i < k then
        (∏ j, a i j) ^ (∑ l, d k l) / (∏ l, a k l) ^ (∑ j, d i j)
        else 1) *
      (∏ i, ∏ j, ∏ l, if j < l then
        a i j ^ d i l / a i l ^ d i j else 1) := by
  classical
  simp_rw [lexFactor, Finset.prod_mul_distrib]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro k _
    exact differentOuterProduct a d i k
  · apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j _
    exact sameOuterProduct a d i j

open GeneralLinear Geometric

universe uF

theorem determinant_leviEmbedding {R : Type*} [CommRing R]
    {n : ℕ} (B : BlockShape n) (m : B.Levi R) :
    determinant (B.leviEmbedding R m) = ∏ i, determinant (m i) := by
  classical
  apply Units.ext
  change Matrix.det
    (Matrix.reindex B.indexEquiv B.indexEquiv
      (Matrix.blockDiagonal' (fun i => (m i).val))) =
    (∏ i, determinant (m i) : Rˣ).val
  rw [Matrix.det_reindex_self,
    (Matrix.blockTriangular_blockDiagonal' (fun i => (m i).val)).det_fintype,
    Units.coe_prod]
  apply Finset.prod_congr rfl
  intro i _
  let e : Fin (B.size i) ≃ {q : B.Index // q.1 = i} :=
    Equiv.ofBijective (fun j => ⟨⟨i, j⟩, rfl⟩) (by
      constructor
      · intro j k h
        simpa using h
      · rintro ⟨⟨k, j⟩, hk⟩
        dsimp only at hk
        subst k
        exact ⟨j, rfl⟩)
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext j k
  change Matrix.blockDiagonal' (fun i => (m i).val) ⟨i,j⟩ ⟨i,k⟩ = (m i).val j k
  simp

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

private theorem determinantNorm_leviEmbedding (m : B.Levi F.Carrier) :
    T.determinantNorm n (B.leviEmbedding F.Carrier m) =
      ∏ i, T.determinantNorm (B.size i) (m i) := by
  change T.normalizedAbsUnits (determinant (B.leviEmbedding F.Carrier m)) =
    ∏ i, T.normalizedAbsUnits (determinant (m i))
  rw [determinant_leviEmbedding, map_prod]

private theorem determinantNorm_sizeTransport {a b : ℕ}
    (h : a = b) (g : GeneralLinear a F.Carrier) :
    T.determinantNorm b (reindex (finCongr h) g) =
      T.determinantNorm a g := by
  subst b
  rfl

private theorem determinantNorm_flattenedComponent
    (m : (B.flatten S).Levi F.Carrier) (i : Fin B.length) (j : Fin (S i).length) :
    T.determinantNorm ((S i).size j) (flattenedLeviProductEquiv F.Carrier B S m i j) =
      T.determinantNorm ((B.flatten S).size (B.flattenBlockEquiv S ⟨i,j⟩))
        (m (B.flattenBlockEquiv S ⟨i,j⟩)) := by
  rw [flattenedLeviProductEquiv_apply]
  exact determinantNorm_sizeTransport T _ _

private theorem outerDeterminantNorm (m : (B.flatten S).Levi F.Carrier)
    (i : Fin B.length) :
    T.determinantNorm (B.size i) ((flattenedLeviEquiv F.Carrier B S m).val i) =
      ∏ j, T.determinantNorm ((S i).size j)
        (flattenedLeviProductEquiv F.Carrier B S m i j) := by
  change T.determinantNorm (B.size i)
    ((S i).leviEmbedding F.Carrier (flattenedLeviProductEquiv F.Carrier B S m i)) = _
  exact determinantNorm_leviEmbedding T (S i) _

private theorem innerBlock (m : (B.flatten S).Levi F.Carrier) (i : Fin B.length) :
    PadicField.TopologicalData.refinedLeviBlock B S i (flattenedLeviEquiv F.Carrier B S m) =
      flattenedLeviProductEquiv F.Carrier B S m i := by
  change (refinedLeviEquiv F.Carrier B S).symm
    (flattenedLeviEquiv F.Carrier B S m) i = _
  simp only [flattenedLeviEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

private theorem flattenProduct {M : Type*} [CommMonoid M]
    (f : Fin (B.flatten S).length → Fin (B.flatten S).length → M) :
    (∏ k, ∏ l, f k l) =
      ∏ i, ∏ j, ∏ k, ∏ l,
        f (B.flattenBlockEquiv S ⟨i,j⟩) (B.flattenBlockEquiv S ⟨k,l⟩) := by
  classical
  symm
  calc
    _ = ∏ q : (i : Fin B.length) × Fin (S i).length,
        ∏ q' : (i : Fin B.length) × Fin (S i).length,
          f (B.flattenBlockEquiv S q) (B.flattenBlockEquiv S q') := by
      rw [Fintype.prod_sigma]
      apply Finset.prod_congr rfl
      intro i _
      apply Finset.prod_congr rfl
      intro j _
      rw [Fintype.prod_sigma]
    _ = _ := by
      apply Fintype.prod_equiv (B.flattenBlockEquiv S)
      intro q
      exact Fintype.prod_equiv (B.flattenBlockEquiv S) _ _ (fun _ => rfl)

private theorem fullModulus :
    (T.composedLeviModulus B S).comp
      (flattenedLeviEquiv F.Carrier B S).toMonoidHom =
        T.leviModulus (B.flatten S) := by
  classical
  apply MonoidHom.ext
  intro m
  let a : (i : Fin B.length) → Fin (S i).length → ℝ≥0ˣ :=
    fun i j => T.determinantNorm ((S i).size j)
      (flattenedLeviProductEquiv F.Carrier B S m i j)
  let d : (i : Fin B.length) → Fin (S i).length → ℕ :=
    fun i j => (S i).size j
  have hflat : T.leviModulus (B.flatten S) m =
      ∏ i, ∏ j, ∏ k, ∏ l,
        if i < k ∨ (i = k ∧ j.val < l.val) then
          a i j ^ d k l / a k l ^ d i j else 1 := by
    rw [T.leviModulus_apply]
    simp only [Finset.prod_filter]
    rw [flattenProduct B S]
    simp_rw [← determinantNorm_flattenedComponent T B S,
      B.flattenBlockEquiv_lt_iff, B.flatten_size_flattenBlockEquiv]
    rfl
  have hcomp : T.composedLeviModulus B S (flattenedLeviEquiv F.Carrier B S m) =
      (∏ i, ∏ k, if i < k then
        (∏ j, a i j) ^ (∑ l, d k l) / (∏ l, a k l) ^ (∑ j, d i j)
        else 1) *
      (∏ i, ∏ j, ∏ l, if j < l then
        a i j ^ d i l / a i l ^ d i j else 1) := by
    change T.leviModulus B (flattenedLeviEquiv F.Carrier B S m).val *
      T.refinedLeviModulus B S (flattenedLeviEquiv F.Carrier B S m) = _
    rw [T.leviModulus_apply, T.refinedLeviModulus_apply]
    simp_rw [outerDeterminantNorm T B S, innerBlock B S, T.leviModulus_apply,
      Finset.prod_filter]
    dsimp only [a, d]
    simp only [BlockShape.sum_eq]
  change T.composedLeviModulus B S (flattenedLeviEquiv F.Carrier B S m) = _
  rw [hcomp, hflat, lexProduct]

end Langlands.Parabolic.FlattenedModulusCalculation

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Geometric

universe uF

/-- The actual composed full modulus restricts to the standard flattened one. -/
theorem composedLeviModulus_flattened {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
    (B : BlockShape n) (S : BlockRefinement B) :
    (T.composedLeviModulus B S).comp
      (flattenedLeviEquiv F.Carrier B S).toMonoidHom =
        T.leviModulus (B.flatten S) :=
  Parabolic.FlattenedModulusCalculation.fullModulus T B S

end Langlands.PadicField.TopologicalData
