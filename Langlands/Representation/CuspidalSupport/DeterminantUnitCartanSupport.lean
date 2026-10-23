import Langlands.Representation.CuspidalSupport.LeviGapVanishing
import Langlands.Representation.CuspidalSupport.DeterminantUnit

noncomputable section

namespace Langlands.CuspidalSupport.LeviAdmissibility

open GeneralLinear

universe uF

variable {n : ℕ} (B : BlockShape n)

/-- Bounded adjacent gaps and zero block sums leave only finitely many tuples. -/
theorem finite_zeroSum_boundedGap (N : ℤ) :
    {lam : ∀ j : Fin B.length, Fin (B.size j) → ℤ |
      (∀ j, Antitone (lam j)) ∧
      (∀ j (b : Fin (B.size j)) (h : b.val + 1 < B.size j),
        lam j b - lam j ⟨b.val + 1, h⟩ < N) ∧
      (∀ j, ∑ b, lam j b = 0)}.Finite := by
  classical
  let last (j : Fin B.length) : Fin (B.size j) :=
    ⟨B.size j - 1, by have := B.positive j; omega⟩
  let norm (lam : ∀ j : Fin B.length, Fin (B.size j) → ℤ) :=
    fun j b => lam j b - lam j (last j)
  let box : Set (∀ j : Fin B.length, Fin (B.size j) → ℤ) :=
    Set.univ.pi fun j => Set.univ.pi fun _ => Set.Icc 0 ((B.size j : ℤ) * |N|)
  apply Set.Finite.of_injOn (f := norm) (t := box)
  · intro lam hlam
    simp only [box, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro j b
    have hm := B.positive j
    constructor
    · have h := hlam.1 j (show b ≤ last j from
        Fin.le_iff_val_le_val.mpr (by dsimp [last]; omega))
      dsimp [norm]
      linarith
    · have h := sub_last_le (lam j) N hm (hlam.2.1 j)
        (B.size j - 1 - b.val) b (by omega)
      have h' : ((B.size j - 1 - b.val : ℕ) : ℤ) * |N| ≤
          (B.size j : ℤ) * |N| :=
        mul_le_mul_of_nonneg_right (by omega) (abs_nonneg N)
      exact h.trans h'
  · intro lam hlam mu hmu heq
    funext j b
    have hs := congrArg (fun x => ∑ b, x j b) heq
    simp only [norm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hlam.2.2 j, hmu.2.2 j] at hs
    have hm : (B.size j : ℤ) ≠ 0 := by have := B.positive j; omega
    have hl : lam j (last j) = mu j (last j) :=
      mul_left_cancel₀ hm (by linarith)
    have hb := congrFun (congrFun heq j) b
    dsimp [norm] at hb
    linarith
  · exact Set.Finite.pi fun j => Set.Finite.pi fun _ => Set.finite_Icc _ _

section Valuation

variable {K : Type uF} [Field K] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/-- Integral invertible matrices have determinant of valuation one. -/
theorem valuation_det_integralRange {m : ℕ} {k : GeneralLinear m K}
    (hk : k ∈ Iwasawa.integralRange v m) :
    v (GeneralLinear.determinant k : K) = 1 := by
  obtain ⟨a, rfl⟩ := hk
  rw [GeneralLinear.determinant, Matrix.GeneralLinearGroup.map_det]
  exact (Valuation.integer.integers v).one_of_isUnit
    (Matrix.GeneralLinearGroup.det a).isUnit

/-- The determinant of a diagonal torus element is its uniformizer to the sum
of its exponents. -/
theorem determinant_torus {m : ℕ} (ϖ : Kˣ) (lam : Fin m → ℤ) :
    GeneralLinear.determinant (Iwasawa.torus ϖ lam) = ϖ ^ (∑ i, lam i) := by
  classical
  have hp (s : Finset (Fin m)) :
      ∏ i ∈ s, ϖ ^ lam i = ϖ ^ (∑ i ∈ s, lam i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [ha, ih, zpow_add]
  apply Units.ext
  change (Matrix.diagonal fun i => ((ϖ ^ lam i : Kˣ) : K)).det = _
  rw [Matrix.det_diagonal, ← Units.coe_prod, hp]

/-- In a Cartan factorization of a determinant-unit matrix, the exponents sum
to zero. This does not assume existence of the factorization. -/
theorem sum_eq_zero_of_cartan {m : ℕ} {ϖ : Kˣ}
    (hϖ : Iwasawa.IsUniformizingElement v ϖ)
    {g k₁ k₂ : GeneralLinear m K} {lam : Fin m → ℤ}
    (hg : g = k₁ * Iwasawa.torus ϖ lam * k₂)
    (hk₁ : k₁ ∈ Iwasawa.integralRange v m)
    (hk₂ : k₂ ∈ Iwasawa.integralRange v m)
    (hdet : v (GeneralLinear.determinant g : K) = 1) :
    ∑ i, lam i = 0 := by
  rw [hg, map_mul, map_mul, Units.val_mul, Units.val_mul, map_mul, map_mul,
    valuation_det_integralRange v hk₁, valuation_det_integralRange v hk₂,
    one_mul, mul_one, determinant_torus, Units.val_zpow_eq_zpow_val, map_zpow₀] at hdet
  exact (zpow_eq_one_iff_right₀ zero_le hϖ.1.ne).mp hdet

end Valuation

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The actual residue-normalized determinant-unit condition forces zero sums
in every block of a product Cartan factorization. -/
theorem block_sums_eq_zero_of_determinantUnit_cartan (T : F.TopologicalData) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ {ϖ : F.Carrierˣ},
      Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ →
      ∀ {g k₁ k₂ : B.Levi F.Carrier}
        {lam : ∀ j : Fin B.length, Fin (B.size j) → ℤ},
        g ∈ determinantUnitSubgroup T B →
        k₁ ∈ integralLevi B → k₂ ∈ integralLevi B →
        g = k₁ * leviTorus B ϖ lam * k₂ →
        ∀ j, ∑ b, lam j b = 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ϖ hϖ g k₁ k₂ lam hg hk₁ hk₂ hfact j
  apply sum_eq_zero_of_cartan (ValuativeRel.valuation F.Carrier) hϖ
    (congrFun hfact j) ((mem_integralLevi B).mp hk₁ j)
    ((mem_integralLevi B).mp hk₂ j)
  have hnorm := (mem_determinantUnitSubgroup_iff_normalizedAbs T B g).mp hg j
  rw [T.normalizedAbs_eq_one_iff_discreteValuation] at hnorm
  change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
    (ValuativeRel.valuation F.Carrier (GeneralLinear.determinant (g j) : F.Carrier)) = 1
      at hnorm
  apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier).injective
  simpa using hnorm

end Padic

end Langlands.CuspidalSupport.LeviAdmissibility
