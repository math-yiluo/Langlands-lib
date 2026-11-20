import Langlands.Representation.Archimedean.RealLeviParabolicIntegration

/-!
# Integration in two real blocks

Specialize the real standard parabolic integration formula to two blocks.
-/

noncomputable section

open MeasureTheory Matrix
open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RealBlockParabolicIntegration

open RealLeviChart RealLeviParabolicIntegration RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK RealLeviBlockHaar.secondCountableTopology_O

local instance (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

private theorem pos_injective (sz : Fin 2 → ℕ) (i : Fin 2) :
    Function.Injective (pos sz i) := by
  intro p q hpq
  apply Fin.ext
  exact Nat.add_left_cancel (by simpa only [val_pos] using congrArg Fin.val hpq)

/-- Two-block coordinates have a row index in the second block and a column index
in the first. -/
private def rectangularIndex (sz : Fin 2 → ℕ) :
    Fin (sz 1) × Fin (sz 0) ≃ Coord sz := by
  let toCoord : Fin (sz 1) × Fin (sz 0) → Coord sz :=
    fun p => ⟨(pos sz 1 p.1, pos sz 0 p.2), by simpa only [cls_pos] using
      (show (0 : Fin 2) < 1 by decide)⟩
  refine Equiv.ofBijective toCoord ⟨?_, ?_⟩
  · intro p q hpq
    exact Prod.ext
      (pos_injective sz 1 (congrArg (fun t : Coord sz => t.1.1) hpq))
      (pos_injective sz 0 (congrArg (fun t : Coord sz => t.1.2) hpq))
  · rintro ⟨⟨i, j⟩, hij⟩
    have hlt : (cls sz j).val < (cls sz i).val := hij
    have hi_lt : (cls sz i).val < 2 := (cls sz i).isLt
    have hi : cls sz i = 1 := by
      apply Fin.ext
      change (cls sz i).val = 1
      omega
    have hj : cls sz j = 0 := by
      apply Fin.ext
      change (cls sz j).val = 0
      omega
    obtain ⟨p, hp⟩ : ∃ p : Fin (sz 1), pos sz 1 p = i := by
      rw [← hi]
      exact pos_cls sz i
    obtain ⟨q, hq⟩ : ∃ q : Fin (sz 0), pos sz 0 q = j := by
      rw [← hj]
      exact pos_cls sz j
    exact ⟨(p, q), Subtype.ext (Prod.ext hp hq)⟩

private def rectangularEquiv (sz : Fin 2 → ℕ) :
    (Fin (sz 1) → Fin (sz 0) → ℝ) ≃ᵐ (Coord sz → ℝ) :=
  (MeasurableEquiv.curry (Fin (sz 1)) (Fin (sz 0)) ℝ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (rectangularIndex sz))

private theorem rectangularEquiv_apply (sz : Fin 2 → ℕ)
    (X : Fin (sz 1) → Fin (sz 0) → ℝ) (p : Fin (sz 1) × Fin (sz 0)) :
    rectangularEquiv sz X (rectangularIndex sz p) = X p.1 p.2 := by
  exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ)
    (rectangularIndex sz) (fun q => X q.1 q.2) p

private theorem measurePreserving_rectangularEquiv (sz : Fin 2 → ℕ) :
    MeasurePreserving (rectangularEquiv sz) volume volume :=
  (volume_measurePreserving_piCongrLeft (fun _ => ℝ) (rectangularIndex sz)).comp
    (RealLeviChartIntegrable.measurePreserving_curry (Fin (sz 1)) (Fin (sz 0))).symm

private theorem cast_pos_zero (sz : Fin 2 → ℕ) (p : Fin (sz 0)) :
    Fin.cast (Fin.sum_univ_two sz) (pos sz 0 p) = Fin.castAdd (sz 1) p := by
  apply Fin.ext
  simp [val_pos, start]

private theorem cast_pos_one (sz : Fin 2 → ℕ) (p : Fin (sz 1)) :
    Fin.cast (Fin.sum_univ_two sz) (pos sz 1 p) = Fin.natAdd (sz 0) p := by
  apply Fin.ext
  simp [val_pos, start]

private theorem forall_pos (sz : Fin 2 → ℕ) {P : Fin (∑ i, sz i) → Prop}
    (h : ∀ i (p : Fin (sz i)), P (pos sz i p)) : ∀ j, P j := by
  intro j
  obtain ⟨p, hp⟩ := pos_cls sz j
  exact hp ▸ h (cls sz j) p

private theorem finTwo_cases : ∀ i : Fin 2, i = 0 ∨ i = 1 := by
  rw [Fin.forall_fin_two]
  exact ⟨Or.inl rfl, Or.inr rfl⟩

/-- View a square matrix unit at an equal rank. -/
private def castGL {m n : ℕ} (h : m = n) (g : Langlands.GeneralLinear n ℝ) :
    Langlands.GeneralLinear m ℝ :=
  h.symm ▸ g

private theorem castGL_apply {m n : ℕ} (h : m = n) (g : Langlands.GeneralLinear n ℝ)
    (i j : Fin m) :
    ((castGL h g : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ) i j =
      (g : Matrix (Fin n) (Fin n) ℝ) (Fin.cast h i) (Fin.cast h j) := by
  subst m
  rfl

private theorem lowerGL_rectangular (sz : Fin 2 → ℕ)
    (X : Fin (sz 1) → Fin (sz 0) → ℝ) :
    lowerGL sz (rectangularEquiv sz X) =
      castGL (Fin.sum_univ_two sz) (RealBlockParabolic.blockLowerGL (Matrix.of X)) := by
  apply Units.ext
  apply Matrix.ext
  refine forall_pos sz fun b p => forall_pos sz fun c q => ?_
  rw [castGL_apply, lowerGL_val]
  change lower sz (rectangularEquiv sz X) (pos sz b p) (pos sz c q) =
    RealBlockParabolic.blockLower (Matrix.of X)
      (Fin.cast (Fin.sum_univ_two sz) (pos sz b p))
      (Fin.cast (Fin.sum_univ_two sz) (pos sz c q))
  simp only [RealBlockParabolic.blockLower, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finTwo_cases b with rfl | rfl <;> rcases finTwo_cases c with rfl | rfl
  · simp only [cast_pos_zero, finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁]
    simp [lower, cls_pos, Matrix.one_apply, (pos_injective sz 0).eq_iff]
  · have hne : pos sz 0 p ≠ pos sz 1 q := by
      intro h
      simpa [cls_pos] using congrArg (cls sz) h
    simp only [cast_pos_zero, cast_pos_one, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    simp [lower, cls_pos, hne]
  · simp only [cast_pos_zero, cast_pos_one, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁, Matrix.of_apply, lower,
      cls_pos, show (0 : Fin 2) < 1 by decide, ↓reduceDIte]
    exact rectangularEquiv_apply sz X (p, q)
  · simp only [cast_pos_one, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂]
    simp [lower, cls_pos, Matrix.one_apply, (pos_injective sz 1).eq_iff]

private theorem blockDiagGL_rectangular (sz : Fin 2 → ℕ)
    (g : ∀ i, Langlands.GeneralLinear (sz i) ℝ) :
    blockDiagGL sz g = castGL (Fin.sum_univ_two sz) (RealBlockParabolic.blockDiagGL (g 0) (g 1)) := by
  apply Units.ext
  apply Matrix.ext
  refine forall_pos sz fun b p => forall_pos sz fun c q => ?_
  rw [castGL_apply, blockDiagGL_val]
  change blockDiagHom sz (fun i => (g i : Matrix (Fin (sz i)) (Fin (sz i)) ℝ))
      (pos sz b p) (pos sz c q) =
    RealBlockParabolic.blockDiag (g 0 : Matrix (Fin (sz 0)) (Fin (sz 0)) ℝ)
      (g 1 : Matrix (Fin (sz 1)) (Fin (sz 1)) ℝ)
      (Fin.cast (Fin.sum_univ_two sz) (pos sz b p))
      (Fin.cast (Fin.sum_univ_two sz) (pos sz c q))
  simp only [RealBlockParabolic.blockDiag, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finTwo_cases b with rfl | rfl <;> rcases finTwo_cases c with rfl | rfl
  · simp only [cast_pos_zero, finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁,
      blockDiagHom_pos_pos_self]
  · simp only [cast_pos_zero, cast_pos_one, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
      blockDiagHom_pos_pos_of_ne sz _ (by decide : (0 : Fin 2) ≠ 1)]
  · simp only [cast_pos_zero, cast_pos_one, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
      blockDiagHom_pos_pos_of_ne sz _ (by decide : (1 : Fin 2) ≠ 0)]
  · simp only [cast_pos_one, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂,
      blockDiagHom_pos_pos_self]

open GramFormula MaximalParabolicIntegration RealLeviTwoBlock in
/-- The Gram bound used for the general formula also gives joint integrability before Fubini. -/
private theorem integrable_levi_product {sz : Fin 2 → ℕ}
    {F : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ}
    (hFs : ContMDiff (matrixModel ℝ (∑ i, sz i)) 𝓘(ℝ, ℂ) ∞ F) (hF : IsModulusCovariant F) :
    Integrable
      (fun p : (∀ i, unitaryCompact ℝ (sz i)) × (Coord sz → ℝ) =>
        F (lowerGL sz p.2 * bd p.1))
      ((Measure.pi fun i => haarK (sz i)).prod volume) := by
  have hcont : Continuous fun p : (∀ i, unitaryCompact ℝ (sz i)) × (Coord sz → ℝ) =>
      F (lowerGL sz p.2 * bd p.1) := by
    refine continuous_comp_of_val hFs ?_
    simp only [Units.val_mul, lowerGL_val]
    exact (continuous_lower_sz.comp continuous_snd).matrix_mul
      (continuous_bd_val.comp continuous_fst)
  obtain ⟨B, hB⟩ := exists_bound hFs
  have hcl : Monotone (cls sz) := cls_monotone
  have hbound : Integrable fun X : Coord sz → ℝ =>
      ∏ l : Fin (∑ i, sz i), gram (l : ℕ) (lower sz X) ^ (-1 : ℝ) :=
    integrable_prod_gram_inv hcl
  refine ((hbound.const_mul B).comp_snd (Measure.pi fun i => haarK (sz i))).mono'
    hcont.aestronglyMeasurable (ae_of_all _ fun p => ?_)
  simpa only [lowerGL_val] using norm_le_gram_inv hF hB (lowerGL sz p.2)
    (by rw [lowerGL_val]; exact gram_zero_lowerC hcl p.2)
    (blockDiagGL_mem_unitaryCompact p.1)

private def blockIntegrand {n a k : ℕ} (h : n = a + k)
    (F : Langlands.GeneralLinear n ℝ → ℂ) (κ₁ : unitaryCompact ℝ a)
    (κ₂ : unitaryCompact ℝ k) (X : Fin k → Fin a → ℝ) : ℂ :=
  F (castGL h (RealBlockParabolic.blockLowerGL (Matrix.of X)) *
    castGL h (RealBlockParabolic.blockDiagGL
      (κ₁ : Langlands.GeneralLinear a ℝ) (κ₂ : Langlands.GeneralLinear k ℝ)))

/-- The fixed-size formula with its general linear group indexed by an equal rank. -/
private def BlockFormula (n a k : ℕ) (h : n = a + k) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ F : Langlands.GeneralLinear n ℝ → ℂ,
      ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ F →
      MaximalParabolicIntegration.IsModulusCovariant F →
      (∀ (κ₁ : unitaryCompact ℝ a) (κ₂ : unitaryCompact ℝ k),
        Integrable (blockIntegrand h F κ₁ κ₂)) ∧
      ∫ κ, F (κ : Langlands.GeneralLinear n ℝ) ∂haarK n =
        (c : ℂ) * ∫ κ₁ : unitaryCompact ℝ a, (∫ κ₂ : unitaryCompact ℝ k,
          (∫ X : Fin k → Fin a → ℝ, blockIntegrand h F κ₁ κ₂ X) ∂haarK k) ∂haarK a

private theorem blockFormula_sum (sz : Fin 2 → ℕ) :
    BlockFormula (∑ i, sz i) (sz 0) (sz 1) (Fin.sum_univ_two sz) := by
  obtain ⟨C, hC, hLevi⟩ := realLeviParabolicIntegration 2 sz
  refine ⟨C, hC, fun F hFs hF => ?_⟩
  obtain ⟨hsections, hformula⟩ := hLevi F hFs hF
  let e := MeasurableEquiv.piFinTwo (fun i => unitaryCompact ℝ (sz i))
  have he : MeasurePreserving e (Measure.pi fun i => haarK (sz i))
      ((haarK (sz 0)).prod (haarK (sz 1))) :=
    measurePreserving_piFinTwo (fun i => haarK (sz i))
  have hX := measurePreserving_rectangularEquiv sz
  have hentry (κ : ∀ i, unitaryCompact ℝ (sz i)) (X : Fin (sz 1) → Fin (sz 0) → ℝ) :
      F (lowerGL sz (rectangularEquiv sz X) * bd κ) =
        blockIntegrand (Fin.sum_univ_two sz) F (e κ).1 (e κ).2 X := by
    unfold bd blockIntegrand
    rw [lowerGL_rectangular, blockDiagGL_rectangular]
    rfl
  constructor
  · intro κ₁ κ₂
    have hsection := hX.integrable_comp_of_integrable (hsections (e.symm (κ₁, κ₂)))
    simpa only [Function.comp_def, hentry, e.apply_symm_apply] using hsection
  · let H : unitaryCompact ℝ (sz 0) × unitaryCompact ℝ (sz 1) → ℂ :=
      fun p => ∫ X : Fin (sz 1) → Fin (sz 0) → ℝ, blockIntegrand (Fin.sum_univ_two sz) F p.1 p.2 X
    have hinner (κ : ∀ i, unitaryCompact ℝ (sz i)) :
        (∫ X : Coord sz → ℝ, F (lowerGL sz X * bd κ)) = H (e κ) := by
      rw [← hX.integral_comp' (fun X => F (lowerGL sz X * bd κ))]
      exact integral_congr_ae (ae_of_all _ (hentry κ))
    have hH : Integrable H ((haarK (sz 0)).prod (haarK (sz 1))) := by
      apply (he.integrable_comp_emb e.measurableEmbedding).mp
      simpa only [Function.comp_def, hinner] using
        (integrable_levi_product (sz := sz) hFs hF).integral_prod_left
    have hcompact :
        (∫ κ, (∫ X : Coord sz → ℝ, F (lowerGL sz X * bd κ)) ∂Measure.pi fun i => haarK (sz i)) =
          ∫ κ₁, (∫ κ₂, H (κ₁, κ₂) ∂haarK (sz 1)) ∂haarK (sz 0) := by
      simp_rw [hinner]
      exact (he.integral_comp' H).trans (integral_prod H hH)
    exact hformula.trans (congrArg (fun z => (C : ℂ) * z) hcompact)

private theorem blockFormula_at_sum {n a k : ℕ} {h : n = a + k}
    (hformula : BlockFormula n a k h) : BlockFormula (a + k) a k rfl := by
  subst n
  exact hformula

end RealBlockParabolicIntegration

open RealBlockParabolicIntegration in
/-- The two-block formula with rectangular Lebesgue coordinates and iterated Haar probabilities. -/
theorem realBlockParabolicIntegration : RealBlockParabolicIntegrationStatement := by
  intro a k
  exact blockFormula_at_sum (blockFormula_sum ![a, k])

end Langlands.Archimedean
