import Langlands.Representation.RankinSelberg.RootCoordinateStatement
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Mathlib.Order.Interval.Finset.Fin

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear
open scoped BigOperators

universe uF

private def tail {G : Type*} [CommMonoid G] {m : ℕ} (a : Fin m → G) (k : ℕ) : G :=
  ∏ j ∈ Finset.univ.filter (k ≤ ·.val), a j

private theorem tail_step {G : Type*} [CommMonoid G] {m : ℕ}
    (a : Fin m → G) (i : Fin m) : tail a i.val = a i * tail a (i.val + 1) := by
  have hs : Finset.univ.filter (fun j : Fin m => i.val ≤ j.val) =
      insert i (Finset.univ.filter (fun j : Fin m => i.val + 1 ≤ j.val)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases he : j = i
      · exact Or.inl he
      · exact Or.inr (by have := Fin.val_ne_of_ne he; omega)
    · rintro (rfl | h) <;> omega
  unfold tail
  rw [hs, Finset.prod_insert]
  simp

private theorem tail_end {G : Type*} [CommMonoid G] {m : ℕ} (a : Fin m → G) :
    tail a m = 1 := by
  apply Finset.prod_eq_one
  intro j hj
  have := (Finset.mem_filter.mp hj).2
  omega

private def diagonalCoords {G : Type*} [CommMonoid G] {m : ℕ}
    (a : Fin m → G) : Fin m → G := fun i => tail a i.val

private theorem diagonalCoords_last {G : Type*} [CommMonoid G] {n : ℕ}
    (a : Fin (n + 1) → G) : diagonalCoords a (Fin.last n) = a (Fin.last n) := by
  rw [diagonalCoords, tail_step, Fin.val_last, tail_end, mul_one]

private theorem diagonalCoords_step {G : Type*} [CommMonoid G] {n : ℕ}
    (a : Fin (n + 1) → G) (i : Fin n) :
    diagonalCoords a i.castSucc = a i.castSucc * diagonalCoords a i.succ :=
  tail_step a i.castSucc

private def rootCoords {G : Type*} [CommGroup G] {n : ℕ}
    (b : Fin (n + 1) → G) : Fin (n + 1) → G :=
  Fin.lastCases (b (Fin.last n)) (fun i => b i.castSucc / b i.succ)

private theorem root_diagonal {G : Type*} [CommGroup G] {n : ℕ}
    (a : Fin (n + 1) → G) : rootCoords (diagonalCoords a) = a := by
  funext i
  induction i using Fin.lastCases with
  | last => simpa [rootCoords] using diagonalCoords_last a
  | cast i => simp [rootCoords, diagonalCoords_step]

private theorem diagonal_root {G : Type*} [CommGroup G] {n : ℕ}
    (b : Fin (n + 1) → G) : diagonalCoords (rootCoords b) = b := by
  funext i
  induction i using Fin.reverseInduction with
  | last => simp [diagonalCoords_last, rootCoords]
  | cast i ih => rw [diagonalCoords_step, ih]; simp [rootCoords]

private theorem diagonalCoords_mul {G : Type*} [CommMonoid G] {m : ℕ}
    (a b : Fin m → G) : diagonalCoords (a * b) = diagonalCoords a * diagonalCoords b := by
  ext i
  change (∏ j ∈ Finset.univ.filter (i.val ≤ ·.val), a j * b j) = _
  exact Finset.prod_mul_distrib

private theorem diagonalCoords_continuous {G : Type*} [CommMonoid G]
    [TopologicalSpace G] [ContinuousMul G] {m : ℕ} :
    Continuous (diagonalCoords : (Fin m → G) → (Fin m → G)) := by
  apply continuous_pi
  intro i
  exact continuous_finsetProd (Finset.univ.filter (i.val ≤ ·.val)) (fun j _ =>
    (continuous_apply j : Continuous (fun a : Fin m → G => a j)))

private theorem rootCoords_continuous {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ} :
    Continuous (rootCoords : (Fin (n + 1) → G) → (Fin (n + 1) → G)) := by
  apply continuous_pi
  intro i
  induction i using Fin.lastCases with
  | last => simpa [rootCoords] using (continuous_apply (Fin.last n) :
      Continuous (fun b : Fin (n + 1) → G => b (Fin.last n)))
  | cast i =>
    simp only [rootCoords, Fin.lastCases_castSucc, div_eq_mul_inv]
    exact continuous_mul.comp
      ((continuous_apply i.castSucc).prodMk
        (continuous_inv.comp (continuous_apply i.succ)))

private def coordinateEquiv {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (n : ℕ) : (Fin (n + 1) → G) ≃ₜ* (Fin (n + 1) → G) where
  toFun := diagonalCoords
  invFun := rootCoords
  left_inv := root_diagonal
  right_inv := diagonal_root
  map_mul' := diagonalCoords_mul
  continuous_toFun := diagonalCoords_continuous
  continuous_invFun := rootCoords_continuous

private theorem diagonalCoords_subgroup {G : Type*} [CommGroup G] {n : ℕ}
    (K : Subgroup G) (a : Fin (n + 1) → G) (ha : ∀ i, a i ∈ K) :
    ∀ i, diagonalCoords a i ∈ K := by
  intro i
  unfold diagonalCoords tail
  exact K.prod_mem (fun j _ => ha j)

private theorem rootCoords_subgroup {G : Type*} [CommGroup G] {n : ℕ}
    (K : Subgroup G) (a : Fin (n + 1) → G) (ha : ∀ i, a i ∈ K) :
    ∀ i, rootCoords a i ∈ K := by
  intro i
  induction i using Fin.lastCases with
  | last => simpa [rootCoords] using ha (Fin.last n)
  | cast i => simpa [rootCoords] using K.div_mem (ha i.castSucc) (ha i.succ)

private theorem diagonalCoords_haar {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G) (hK : MeasurableSet (K : Set G))
    (hμK : μ (K : Set G) = 1) (n : ℕ) :
    Measure.map (diagonalCoords : (Fin (n + 1) → G) → _) (Measure.pi (fun _ => μ)) =
      Measure.pi (fun _ : Fin (n + 1) => μ) := by
  let ν : Measure (Fin (n + 1) → G) := Measure.pi (fun _ => μ)
  let e := coordinateEquiv (G := G) n
  let S : Set (Fin (n + 1) → G) := Set.univ.pi (fun _ => (K : Set G))
  have hS : MeasurableSet S := MeasurableSet.univ_pi (fun _ => hK)
  have hνS : ν S = 1 := by simp [ν, S, Measure.pi_pi, hμK]
  have hpre : e ⁻¹' S = S := by
    ext a
    change (∀ i ∈ Set.univ, diagonalCoords a i ∈ K) ↔ ∀ i ∈ Set.univ, a i ∈ K
    simp only [Set.mem_univ, forall_const]
    constructor
    · intro h i
      have := rootCoords_subgroup K (diagonalCoords a) h i
      rwa [root_diagonal] at this
    · exact diagonalCoords_subgroup K a
  have hmS : Measure.map e ν S = 1 := by
    have hm : Measurable (e : (Fin (n + 1) → G) → _) :=
      diagonalCoords_continuous.measurable
    rw [Measure.map_apply hm hS, hpre, hνS]
  have heq := Measure.isMulLeftInvariant_eq_smul (Measure.map e ν) ν
  have hc := congrArg (fun η : Measure (Fin (n + 1) → G) => η S) heq
  have hc' : (Measure.haarScalarFactor (Measure.map e ν) ν : ENNReal) = 1 := by
    simpa [Measure.smul_apply, hνS, hmS] using hc.symm
  change Measure.map e ν = ν
  rw [heq]
  have hc'' : Measure.haarScalarFactor (Measure.map e ν) ν = 1 := by exact_mod_cast hc'
  rw [hc'', one_smul]

private theorem prod_lower {G : Type*} [CommMonoid G] {m : ℕ} (j : Fin m) (b : G) :
    (∏ i : Fin m, if i ≤ j then b else 1) = b ^ (j.val + 1) := by
  rw [← Finset.prod_filter]
  have hs : Finset.univ.filter (fun i : Fin m => i ≤ j) = Finset.Iic j := by
    ext i; simp
  rw [hs, Finset.prod_const, Fin.card_Iic]

private theorem prod_upper {G : Type*} [CommMonoid G] {n : ℕ} (j : Fin (n + 1)) (b : G) :
    (∏ i : Fin (n + 1), if j < i then b else 1) = b ^ (n - j.val) := by
  rw [← Finset.prod_filter]
  have hs : Finset.univ.filter (fun i : Fin (n + 1) => j < i) = Finset.Ioi j := by
    ext i; simp
  rw [hs, Finset.prod_const, Fin.card_Ioi, Nat.add_sub_cancel]

private theorem prod_diagonalCoords {G : Type*} [CommMonoid G] {m : ℕ} (a : Fin m → G) :
    (∏ i, diagonalCoords a i) = ∏ i, a i ^ (i.val + 1) := by
  simp only [diagonalCoords, tail, Finset.prod_filter]
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl (fun i _ => prod_lower i (a i))

private theorem diagonalCoords_ratio {G : Type*} [CommGroup G] {m : ℕ}
    (a : Fin m → G) (i j : Fin m) (hij : i < j) :
    diagonalCoords a i / diagonalCoords a j =
      ∏ k : Fin m, if i ≤ k ∧ k < j then a k else 1 := by
  simp only [diagonalCoords, tail, Finset.prod_filter]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro k _
  by_cases hi : i ≤ k <;> by_cases hj : j ≤ k
  · simp [hi, hj, show ¬k < j from not_lt.mpr hj]
  · simp [hi, hj, show k < j from lt_of_not_ge hj]
  · exact False.elim (hi (le_trans (le_of_lt hij) hj))
  · simp [hi, hj]

private theorem diagonalCoords_modulus {G : Type*} [CommGroup G] {n : ℕ}
    (a : Fin (n + 1) → G) :
    (∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (i < ·),
      diagonalCoords a i / diagonalCoords a j) =
        ∏ k, a k ^ ((k.val + 1) * (n - k.val)) := by
  classical
  have hpair (i j : Fin (n + 1)) :
      (if i < j then diagonalCoords a i / diagonalCoords a j else 1) =
        ∏ k, if i ≤ k ∧ k < j then a k else 1 := by
    by_cases h : i < j
    · simpa [h] using diagonalCoords_ratio a i j h
    · rw [ite_eq_right h]
      symm
      apply Finset.prod_eq_one
      intro k _
      exact ite_eq_right (fun hk => h (lt_of_le_of_lt hk.1 hk.2))
  simp only [Finset.prod_filter]
  simp_rw [hpair]
  calc
    _ = ∏ i : Fin (n + 1), ∏ k : Fin (n + 1), ∏ j : Fin (n + 1),
        if i ≤ k ∧ k < j then a k else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      exact Finset.prod_comm
    _ = ∏ k : Fin (n + 1), ∏ i : Fin (n + 1), ∏ j : Fin (n + 1),
        if i ≤ k ∧ k < j then a k else 1 := Finset.prod_comm
    _ = ∏ k : Fin (n + 1), ∏ i : Fin (n + 1),
        if i ≤ k then a k ^ (n - k.val) else 1 := by
      apply Finset.prod_congr rfl
      intro k _
      apply Finset.prod_congr rfl
      intro i _
      by_cases h : i ≤ k
      · simpa [h] using prod_upper k (a k)
      · simp [h]
    _ = ∏ k, a k ^ ((k.val + 1) * (n - k.val)) := by
      apply Finset.prod_congr rfl
      intro k _
      rw [prod_lower, ← pow_mul, Nat.mul_comm]

/-- The cumulative-product coordinates preserve normalized torus measure and
have the explicit determinant, row and positive-modulus formulas. -/
theorem rootCoordinateChange {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    RootCoordinateChangeStatement F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let : SecondCountableTopology F.Carrierˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let : MeasurableSpace F.Carrierˣ := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  dsimp only [RootCoordinateChangeStatement]
  refine ⟨diagonalCoords_continuous, rootCoords_continuous,
    root_diagonal, diagonal_root, diagonalCoords_mul, ?_, ?_⟩
  · let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
    let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
    have : T2Space F.Carrier := inferInstance
    exact diagonalCoords_haar (localMultiplicativeHaar F.Carrier)
      (integralUnits (ValuativeRel.valuation F.Carrier).integer)
      ((integralUnits_isOpen _ (Valuation.isOpen_integer
        (v := ValuativeRel.valuation F.Carrier))).measurableSet)
      (localMultiplicativeHaar_integerUnits F.Carrier) n
  · intro a
    refine ⟨?_, diagonalCoords_last a, ?_, ?_, ?_⟩
    · intro i
      change diagonalCoords a i.castSucc / diagonalCoords a i.succ = a i.castSucc
      rw [diagonalCoords_step, mul_div_cancel_right]
    · change Matrix.det (Iwasawa.diagonalUnits (diagonalCoords a)).val = _
      rw [Iwasawa.diagonalUnits_val, Matrix.det_diagonal]
      simpa only [Units.coe_prod, Units.val_pow_eq_pow_val] using
        congrArg (fun z : F.Carrierˣ => (z : F.Carrier)) (prod_diagonalCoords a)
    · intro k
      funext j
      change ((Iwasawa.diagonalUnits (diagonalCoords a)).val * k.val) (Fin.last n) j = _
      rw [Iwasawa.diagonalUnits_val, Matrix.diagonal_mul, diagonalCoords_last]
      rfl
    · let φ : F.Carrierˣ →* ℝ :=
        { toFun := fun z => T.normalizedAbs (z : F.Carrier)
          map_one' := T.normalizedAbs_one
          map_mul' := fun x y => T.normalizedAbs_mul (x : F.Carrier) (y : F.Carrier) }
      have h := congrArg φ (diagonalCoords_modulus a)
      simp only [map_prod, map_pow] at h
      simpa only [φ, MonoidHom.coe_mk, OneHom.coe_mk,
        diagonalCoords, tail, Fin.le_def] using h

end Langlands.RankinSelberg
