import Langlands.BushnellKutzko.LevelZeroCycle

/-! # The element `Π` and injectivity of compression by `diag(ϖ, 1, …, 1)` -/

open Matrix ValuativeRel Langlands.Jacquet

noncomputable section

namespace Langlands.BushnellKutzko.LevelZero

universe uF uV uW

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {e f : ℕ}

section Uniformizer

variable {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
include hϖ

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem uniformizer_ne_zero' : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem val_uniformizer_lt_one : valuation F (ϖ : F) < 1 :=
  (valuation F).mem_maximalIdeal_iff.mp
    ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem val_uniformizer_mul_lt_one {x : F} (hx : valuation F x ≤ 1) :
    valuation F ((ϖ : F) * x) < 1 := by
  rw [map_mul]
  calc valuation F (ϖ : F) * valuation F x ≤ valuation F (ϖ : F) * 1 := mul_le_mul' le_rfl hx
    _ < 1 := by rw [mul_one]; exact val_uniformizer_lt_one hϖ

theorem val_uniformizer_inv_mul_le_one {x : F} (hx : valuation F x < 1) :
    valuation F ((ϖ : F)⁻¹ * x) ≤ 1 := by
  have hmem : (⟨x, hx.le⟩ : 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] :=
    (valuation F).mem_maximalIdeal_iff.mpr hx
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
    Ideal.mem_span_singleton'] at hmem
  obtain ⟨y, hy⟩ := hmem
  have hx' : x = (y : F) * ϖ := by
    have := congrArg Subtype.val hy
    simpa using this.symm
  rw [hx', mul_comm (y : F), ← mul_assoc, inv_mul_cancel₀ (uniformizer_ne_zero' hϖ), one_mul]
  exact y.2

end Uniformizer

section Pi

variable {ϖ : 𝒪[F]}

/-- The diagonal entries of `diag(ϖ, 1, …, 1)` (by blocks). -/
def scaleDiag (ϖ : 𝒪[F]) (he : 0 < e) : Fin f × Fin e → F :=
  fun p => if p.2 = ⟨0, he⟩ then (ϖ : F) else 1

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem scaleDiag_ne_zero (hϖ : Irreducible ϖ) (he : 0 < e) (p : Fin f × Fin e) :
    scaleDiag ϖ he p ≠ 0 := by
  unfold scaleDiag
  split_ifs
  · exact uniformizer_ne_zero' hϖ
  · exact one_ne_zero

/-- The element `diag(ϖ, 1, …, 1)`, by blocks. -/
def aElt (hϖ : Irreducible ϖ) (he : 0 < e) : GL (Fin f × Fin e) F :=
  ⟨Matrix.diagonal (scaleDiag ϖ he), Matrix.diagonal fun p => (scaleDiag ϖ he p)⁻¹,
    by
      rw [Matrix.diagonal_mul_diagonal]
      ext p q
      by_cases h : p = q
      · subst h; simp [mul_inv_cancel₀ (scaleDiag_ne_zero hϖ he p)]
      · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h],
    by
      rw [Matrix.diagonal_mul_diagonal]
      ext p q
      by_cases h : p = q
      · subst h; simp [inv_mul_cancel₀ (scaleDiag_ne_zero hϖ he p)]
      · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]⟩

/-- The block permutation `w₀ = cyc (e - 1)`. -/
abbrev w0 (e : ℕ) : Equiv.Perm (Fin e) := cyc (e - 1)

/-- The element `Π = diag(ϖ, 1, …, 1) · P_{w₀}`. -/
def piElt (hϖ : Irreducible ϖ) (he : 0 < e) : GL (Fin f × Fin e) F :=
  aElt hϖ he * permGL F (w0 e)

theorem w0_val (he : 0 < e) (j : Fin e) :
    (w0 e j).val = if j.val < e - 1 then j.val + 1 else 0 := by
  rw [w0, cyc_val (by omega)]
  split_ifs <;> omega

theorem w0_symm_val (he : 0 < e) (i : Fin e) :
    ((w0 e).symm i).val = if i.val = 0 then e - 1 else i.val - 1 := by
  have h := w0_val he ((w0 e).symm i)
  rw [Equiv.apply_symm_apply] at h
  split_ifs at h ⊢ <;> omega

/-- Conjugation by `Π` on matrices. -/
def piConj (ϖ : 𝒪[F]) (he : 0 < e) (M : Matrix (Fin f × Fin e) (Fin f × Fin e) F) :
    Matrix (Fin f × Fin e) (Fin f × Fin e) F :=
  Matrix.of fun p q => scaleDiag ϖ he p *
    M (p.1, (w0 e).symm p.2) (q.1, (w0 e).symm q.2) * (scaleDiag ϖ he q)⁻¹

/-- Conjugation by `Π⁻¹` on matrices. -/
def piInvConj (ϖ : 𝒪[F]) (he : 0 < e) (M : Matrix (Fin f × Fin e) (Fin f × Fin e) F) :
    Matrix (Fin f × Fin e) (Fin f × Fin e) F :=
  Matrix.of fun p q => (scaleDiag ϖ he (p.1, w0 e p.2))⁻¹ *
    M (p.1, w0 e p.2) (q.1, w0 e q.2) * scaleDiag ϖ he (q.1, w0 e q.2)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem piConj_apply (ϖ : 𝒪[F]) (he : 0 < e) (M : Matrix (Fin f × Fin e) (Fin f × Fin e) F)
    (p q : Fin f × Fin e) :
    piConj ϖ he M p q = scaleDiag ϖ he p *
      M (p.1, (w0 e).symm p.2) (q.1, (w0 e).symm q.2) * (scaleDiag ϖ he q)⁻¹ := rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem piInvConj_apply (ϖ : 𝒪[F]) (he : 0 < e) (M : Matrix (Fin f × Fin e) (Fin f × Fin e) F)
    (p q : Fin f × Fin e) :
    piInvConj ϖ he M p q = (scaleDiag ϖ he (p.1, w0 e p.2))⁻¹ *
      M (p.1, w0 e p.2) (q.1, w0 e q.2) * scaleDiag ϖ he (q.1, w0 e q.2) := rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coe_piElt_conj (hϖ : Irreducible ϖ) (he : 0 < e) (x : GL (Fin f × Fin e) F) :
    ((piElt hϖ he * x * (piElt hϖ he)⁻¹ : GL (Fin f × Fin e) F) :
      Matrix (Fin f × Fin e) (Fin f × Fin e) F) = piConj ϖ he x := by
  have h : piElt hϖ he * x * (piElt hϖ he)⁻¹ =
      aElt hϖ he * (permGL F (w0 e) * x * (permGL F (w0 e))⁻¹) * (aElt hϖ he)⁻¹ := by
    rw [piElt]; group
  rw [h]
  simp only [Units.val_mul]
  rw [permGL_conj]
  ext p q
  simp [piConj, aElt, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coe_piElt_inv_conj (hϖ : Irreducible ϖ) (he : 0 < e) (x : GL (Fin f × Fin e) F) :
    (((piElt hϖ he)⁻¹ * x * piElt hϖ he : GL (Fin f × Fin e) F) :
      Matrix (Fin f × Fin e) (Fin f × Fin e) F) = piInvConj ϖ he x := by
  have h : (piElt hϖ he)⁻¹ * x * piElt hϖ he =
      permGL F (w0 e)⁻¹ * ((aElt hϖ he)⁻¹ * x * aElt hϖ he) * (permGL F (w0 e)⁻¹)⁻¹ := by
    rw [piElt, permGL_inv, inv_inv]; group
  rw [h, Units.val_mul, Units.val_mul, permGL_conj]
  ext p q
  simp [piInvConj, aElt, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc,
    Equiv.Perm.inv_def, Equiv.symm_symm]

section Normalize

variable (hϖ : Irreducible ϖ) (he : 0 < e)
include hϖ

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem conj_cancel (y : F) : (ϖ : F) * y * (ϖ : F)⁻¹ = y := by
  have := uniformizer_ne_zero' hϖ
  field_simp

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem conj_cancel' (y : F) : (ϖ : F)⁻¹ * y * (ϖ : F) = y := by
  have := uniformizer_ne_zero' hϖ
  field_simp

/-- Conjugation by `Π` preserves the radical of the standard principal order. -/
theorem InRad.piConj {M : Matrix (Fin f × Fin e) (Fin f × Fin e) F} (hM : InRad M) :
    InRad (piConj ϖ he M) := by
  intro p q
  have hM' : valuation F (M (p.1, (w0 e).symm p.2) (q.1, (w0 e).symm q.2)) ≤ 1 ∧
      ((w0 e).symm p.2 ≤ (w0 e).symm q.2 →
        valuation F (M (p.1, (w0 e).symm p.2) (q.1, (w0 e).symm q.2)) < 1) :=
    hM (p.1, (w0 e).symm p.2) (q.1, (w0 e).symm q.2)
  have hpv := w0_symm_val he p.2
  have hqv := w0_symm_val he q.2
  have hpe := p.2.isLt
  have hqe := q.2.isLt
  rw [piConj_apply]
  simp only [scaleDiag]
  by_cases hp : p.2 = ⟨0, he⟩
  · have hp' : p.2.val = 0 := by rw [hp]
    by_cases hq : q.2 = ⟨0, he⟩
    · have hq' : q.2.val = 0 := by rw [hq]
      rw [ite_eq_left hp, ite_eq_left hq, conj_cancel hϖ]
      refine ⟨hM'.1, fun _ => hM'.2 ?_⟩
      rw [Fin.le_def]
      split_ifs at hpv hqv
      omega
    · rw [ite_eq_left hp, ite_eq_right hq, inv_one, mul_one]
      exact ⟨(val_uniformizer_mul_lt_one hϖ hM'.1).le,
        fun _ => val_uniformizer_mul_lt_one hϖ hM'.1⟩
  · have hp' : p.2.val ≠ 0 := fun h => hp (Fin.ext h)
    by_cases hq : q.2 = ⟨0, he⟩
    · have hq' : q.2.val = 0 := by rw [hq]
      rw [ite_eq_right hp, ite_eq_left hq, one_mul, mul_comm]
      refine ⟨val_uniformizer_inv_mul_le_one hϖ (hM'.2 ?_), fun h => ?_⟩
      · rw [Fin.le_def]; split_ifs at hpv hqv <;> omega
      · rw [Fin.le_def] at h; omega
    · have hq' : q.2.val ≠ 0 := fun h => hq (Fin.ext h)
      rw [ite_eq_right hp, ite_eq_right hq, one_mul, inv_one, mul_one]
      refine ⟨hM'.1, fun h => hM'.2 ?_⟩
      rw [Fin.le_def] at h ⊢; split_ifs at hpv hqv <;> omega

/-- Conjugation by `Π` preserves the standard principal order. -/
theorem InOrd.piConj {M : Matrix (Fin f × Fin e) (Fin f × Fin e) F} (hM : InOrd M) :
    InOrd (piConj ϖ he M) := by
  intro p q
  have hM' : valuation F (M (p.1, (w0 e).symm p.2) (q.1, (w0 e).symm q.2)) ≤ 1 ∧
      ((w0 e).symm p.2 < (w0 e).symm q.2 →
        valuation F (M (p.1, (w0 e).symm p.2) (q.1, (w0 e).symm q.2)) < 1) :=
    hM (p.1, (w0 e).symm p.2) (q.1, (w0 e).symm q.2)
  have hpv := w0_symm_val he p.2
  have hqv := w0_symm_val he q.2
  have hpe := p.2.isLt
  have hqe := q.2.isLt
  rw [piConj_apply]
  simp only [scaleDiag]
  by_cases hp : p.2 = ⟨0, he⟩
  · have hp' : p.2.val = 0 := by rw [hp]
    by_cases hq : q.2 = ⟨0, he⟩
    · have hq' : q.2.val = 0 := by rw [hq]
      rw [ite_eq_left hp, ite_eq_left hq, conj_cancel hϖ]
      refine ⟨hM'.1, fun h => ?_⟩
      rw [Fin.lt_def] at h; omega
    · rw [ite_eq_left hp, ite_eq_right hq, inv_one, mul_one]
      exact ⟨(val_uniformizer_mul_lt_one hϖ hM'.1).le,
        fun _ => val_uniformizer_mul_lt_one hϖ hM'.1⟩
  · have hp' : p.2.val ≠ 0 := fun h => hp (Fin.ext h)
    by_cases hq : q.2 = ⟨0, he⟩
    · have hq' : q.2.val = 0 := by rw [hq]
      rw [ite_eq_right hp, ite_eq_left hq, one_mul, mul_comm]
      refine ⟨val_uniformizer_inv_mul_le_one hϖ (hM'.2 ?_), fun h => ?_⟩
      · rw [Fin.lt_def]; split_ifs at hpv hqv <;> omega
      · rw [Fin.lt_def] at h; omega
    · have hq' : q.2.val ≠ 0 := fun h => hq (Fin.ext h)
      rw [ite_eq_right hp, ite_eq_right hq, one_mul, inv_one, mul_one]
      refine ⟨hM'.1, fun h => hM'.2 ?_⟩
      rw [Fin.lt_def] at h ⊢; split_ifs at hpv hqv <;> omega

/-- Conjugation by `Π⁻¹` preserves the radical of the standard principal order. -/
theorem InRad.piInvConj {M : Matrix (Fin f × Fin e) (Fin f × Fin e) F} (hM : InRad M) :
    InRad (piInvConj ϖ he M) := by
  intro p q
  have hM' : valuation F (M (p.1, w0 e p.2) (q.1, w0 e q.2)) ≤ 1 ∧
      (w0 e p.2 ≤ w0 e q.2 → valuation F (M (p.1, w0 e p.2) (q.1, w0 e q.2)) < 1) :=
    hM (p.1, w0 e p.2) (q.1, w0 e q.2)
  have hpv := w0_val he p.2
  have hqv := w0_val he q.2
  have hpe := p.2.isLt
  have hqe := q.2.isLt
  rw [piInvConj_apply]
  simp only [scaleDiag]
  by_cases hp : w0 e p.2 = ⟨0, he⟩
  · have hp' : (w0 e p.2).val = 0 := by rw [hp]
    by_cases hq : w0 e q.2 = ⟨0, he⟩
    · have hq' : (w0 e q.2).val = 0 := by rw [hq]
      rw [ite_eq_left hp, ite_eq_left hq, conj_cancel' hϖ]
      refine ⟨hM'.1, fun _ => hM'.2 ?_⟩
      rw [Fin.le_def]; omega
    · have hq' : (w0 e q.2).val ≠ 0 := fun h => hq (Fin.ext h)
      rw [ite_eq_left hp, ite_eq_right hq, mul_one]
      refine ⟨val_uniformizer_inv_mul_le_one hϖ (hM'.2 ?_), fun h => ?_⟩
      · rw [Fin.le_def]; omega
      · rw [Fin.le_def] at h; split_ifs at hpv hqv <;> omega
  · have hp' : (w0 e p.2).val ≠ 0 := fun h => hp (Fin.ext h)
    by_cases hq : w0 e q.2 = ⟨0, he⟩
    · rw [ite_eq_right hp, ite_eq_left hq, inv_one, one_mul]
      exact ⟨(val_uniformizer_mul_lt_one hϖ hM'.1).le |>.trans_eq' (by rw [mul_comm]),
        fun _ => (val_uniformizer_mul_lt_one hϖ hM'.1).trans_eq' (by rw [mul_comm])⟩
    · have hq' : (w0 e q.2).val ≠ 0 := fun h => hq (Fin.ext h)
      rw [ite_eq_right hp, ite_eq_right hq, inv_one, one_mul, mul_one]
      refine ⟨hM'.1, fun h => hM'.2 ?_⟩
      rw [Fin.le_def] at h ⊢; split_ifs at hpv hqv <;> omega

/-- Conjugation by `Π⁻¹` preserves the standard principal order. -/
theorem InOrd.piInvConj {M : Matrix (Fin f × Fin e) (Fin f × Fin e) F} (hM : InOrd M) :
    InOrd (piInvConj ϖ he M) := by
  intro p q
  have hM' : valuation F (M (p.1, w0 e p.2) (q.1, w0 e q.2)) ≤ 1 ∧
      (w0 e p.2 < w0 e q.2 → valuation F (M (p.1, w0 e p.2) (q.1, w0 e q.2)) < 1) :=
    hM (p.1, w0 e p.2) (q.1, w0 e q.2)
  have hpv := w0_val he p.2
  have hqv := w0_val he q.2
  have hpe := p.2.isLt
  have hqe := q.2.isLt
  rw [piInvConj_apply]
  simp only [scaleDiag]
  by_cases hp : w0 e p.2 = ⟨0, he⟩
  · have hp' : (w0 e p.2).val = 0 := by rw [hp]
    by_cases hq : w0 e q.2 = ⟨0, he⟩
    · have hq' : (w0 e q.2).val = 0 := by rw [hq]
      rw [ite_eq_left hp, ite_eq_left hq, conj_cancel' hϖ]
      refine ⟨hM'.1, fun h => ?_⟩
      rw [Fin.lt_def] at h; split_ifs at hpv hqv <;> omega
    · have hq' : (w0 e q.2).val ≠ 0 := fun h => hq (Fin.ext h)
      rw [ite_eq_left hp, ite_eq_right hq, mul_one]
      refine ⟨val_uniformizer_inv_mul_le_one hϖ (hM'.2 ?_), fun h => ?_⟩
      · rw [Fin.lt_def]; omega
      · rw [Fin.lt_def] at h; split_ifs at hpv hqv <;> omega
  · have hp' : (w0 e p.2).val ≠ 0 := fun h => hp (Fin.ext h)
    by_cases hq : w0 e q.2 = ⟨0, he⟩
    · rw [ite_eq_right hp, ite_eq_left hq, inv_one, one_mul]
      exact ⟨(val_uniformizer_mul_lt_one hϖ hM'.1).le |>.trans_eq' (by rw [mul_comm]),
        fun _ => (val_uniformizer_mul_lt_one hϖ hM'.1).trans_eq' (by rw [mul_comm])⟩
    · have hq' : (w0 e q.2).val ≠ 0 := fun h => hq (Fin.ext h)
      rw [ite_eq_right hp, ite_eq_right hq, inv_one, one_mul, mul_one]
      refine ⟨hM'.1, fun h => hM'.2 ?_⟩
      rw [Fin.lt_def] at h ⊢; split_ifs at hpv hqv <;> omega

end Normalize

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem piConj_sub_one (hϖ : Irreducible ϖ) (he : 0 < e) (M : Matrix (Fin f × Fin e) (Fin f × Fin e) F) :
    piConj ϖ he (M - 1) = piConj ϖ he M - 1 := by
  ext p q
  simp only [piConj, Matrix.of_apply, Matrix.sub_apply, sub_mul, mul_sub]
  congr 1
  by_cases h : p = q
  · subst h; simp [mul_inv_cancel₀ (scaleDiag_ne_zero hϖ he p)]
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne]
    · simp
    · intro h'
      apply h
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h'
      exact Prod.ext h'.1 h'.2

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem piInvConj_sub_one (hϖ : Irreducible ϖ) (he : 0 < e)
    (M : Matrix (Fin f × Fin e) (Fin f × Fin e) F) :
    piInvConj ϖ he (M - 1) = piInvConj ϖ he M - 1 := by
  ext p q
  simp only [piInvConj, Matrix.of_apply, Matrix.sub_apply, sub_mul, mul_sub]
  congr 1
  by_cases h : p = q
  · subst h; simp [inv_mul_cancel₀ (scaleDiag_ne_zero hϖ he _)]
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne]
    · simp
    · intro h'
      apply h
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h'
      exact Prod.ext h'.1 h'.2

/-- `Π` normalizes `U^1(𝔄)`. -/
theorem piElt_conj_mem_J1 (hϖ : Irreducible ϖ) (he : 0 < e) {x : GL (Fin f × Fin e) F}
    (hx : x ∈ J1 F e f) : piElt hϖ he * x * (piElt hϖ he)⁻¹ ∈ J1 F e f := by
  refine mem_J1_of_inRad ?_ ?_
  · rw [coe_piElt_conj, ← piConj_sub_one hϖ]
    exact hx.2.piConj hϖ he
  · have : (piElt hϖ he * x * (piElt hϖ he)⁻¹)⁻¹ = piElt hϖ he * x⁻¹ * (piElt hϖ he)⁻¹ := by
      group
    rw [this, coe_piElt_conj, ← piConj_sub_one hϖ]
    exact ((J1 F e f).inv_mem hx).2.piConj hϖ he

/-- `Π⁻¹` normalizes `U^1(𝔄)`. -/
theorem piElt_inv_conj_mem_J1 (hϖ : Irreducible ϖ) (he : 0 < e) {x : GL (Fin f × Fin e) F}
    (hx : x ∈ J1 F e f) : (piElt hϖ he)⁻¹ * x * piElt hϖ he ∈ J1 F e f := by
  refine mem_J1_of_inRad ?_ ?_
  · rw [coe_piElt_inv_conj, ← piInvConj_sub_one hϖ]
    exact hx.2.piInvConj hϖ he
  · have : ((piElt hϖ he)⁻¹ * x * piElt hϖ he)⁻¹ = (piElt hϖ he)⁻¹ * x⁻¹ * piElt hϖ he := by
      group
    rw [this, coe_piElt_inv_conj, ← piInvConj_sub_one hϖ]
    exact ((J1 F e f).inv_mem hx).2.piInvConj hϖ he

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem piElt_mul_permGL (hϖ : Irreducible ϖ) (he : 0 < e) :
    piElt hϖ he * permGL F (f := f) (w0 e)⁻¹ = aElt hϖ he := by
  rw [piElt, mul_assoc, ← permGL_mul, mul_inv_cancel, permGL_one, mul_one]

end Pi

section Principal

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GL (Fin f × Fin e) F) V) (hπ : IsSmooth π)
  (K : OpenSubgroup (GL (Fin f × Fin e) F)) (hK : IsCompact (K : Set (GL (Fin f × Fin e) F)))

variable [Fintype 𝓀[F]]

/-- **Principal lemma at level zero.** Compression by `diag(ϖ, 1, …, 1)` (by blocks) is zero on an
intertwining map from a representation of `U(𝔄)` that is trivial on `U^1(𝔄) = K` and cuspidal on
the first block only when the map is zero. -/
theorem compressionMap_aElt_comp_eq_zero {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (he : 0 < e)
    (hKJ : K.toSubgroup = J1 F e f)
    {W : Type uW} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (J0 F e f) W)
    (hρ1 : ∀ x : J0 F e f, (x : GL (Fin f × Fin e) F) ∈ J1 F e f → ρ x = 1)
    (hcusp : ∀ (m : Fin e) (hm : (⟨0, he⟩ : Fin e) < m) (r : ℕ), 0 < r → r < f →
      ∑ Z : Matrix (Fin f) (Fin f) 𝓀[F],
        ρ ⟨pairGL hm.ne (diagU (unipLift r Z) 1),
          diagU_mem_J0 hm (isIntGL_unipLift r Z) isIntGL_one⟩ = 0)
    (φ : W →ₗ[ℂ] V) (hφ : ∀ (x : J0 F e f) (w : W), φ (ρ x w) = π x (φ w))
    (h : (compressionMap π hπ K hK (aElt hϖ he)).comp φ = 0) : φ = 0 := by
  have hJK : ∀ x, x ∈ K ↔ x ∈ J1 F e f := fun x => by
    change x ∈ K.toSubgroup ↔ _; rw [hKJ]
  have hφfix : ∀ w, φ w ∈ fixedVectors π K.toSubgroup := by
    intro w k
    have hk : (k : GL (Fin f × Fin e) F) ∈ J1 F e f := (hJK k.val).mp k.property
    change π k (φ w) = φ w
    rw [← hφ ⟨k, J1_le_J0 hk⟩, hρ1 _ hk]
    rfl
  refine compressionMap_cyc_comp_eq_zero π hπ K hK he hKJ ρ hρ1 hcusp φ hφ (e - 1) (by omega) ?_
  ext w
  set c : GL (Fin f × Fin e) F := permGL F (cyc (e - 1))⁻¹ with hc
  have hcw : compressionMap π hπ K hK c (φ w) ∈ fixedVectors π K.toSubgroup :=
    Compact.averageMap_mem_fixedVectors π hπ K hK _
  have hmul := compressionMap_mul_of_factor π hπ K hK (piElt hϖ he) c
    (fun κ hκ => ⟨κ, 1, by group,
      (hJK _).mpr (piElt_conj_mem_J1 hϖ he ((hJK κ).mp hκ)),
      by simp [(hJK 1).mpr (J1 F e f).one_mem]⟩) (φ w) (hφfix w)
  rw [hc, piElt_mul_permGL] at hmul
  rw [compressionMap_of_normalizes π hπ K hK (piElt hϖ he)
    (fun κ hκ => (hJK _).mpr (piElt_inv_conj_mem_J1 hϖ he ((hJK κ).mp hκ))) _ hcw] at hmul
  have h0 : π (piElt hϖ he) (compressionMap π hπ K hK c (φ w)) = 0 := by
    rw [hmul]; exact LinearMap.congr_fun h w
  have := congrArg (π (piElt hϖ he)⁻¹) h0
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    map_zero] at this
  exact this

end Principal

end Langlands.BushnellKutzko.LevelZero
