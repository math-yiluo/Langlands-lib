import Langlands.Global.RankinSelberg.DualExpansionPeriodStep

/-! # The rectangular side of the dual expansion and its rank step -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global
open Langlands.Automorphic.CuspidalWhittaker (IsPeriodic ratVec ratVec_apply sqZeroUnit
  sqZeroUnit_val)

variable {F : Type u} [Field F] [NumberField F]

local instance dualRStepSchemeAffine (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dualRStepSchemeSmooth (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

local instance dualRStepAdelesLocallyCompact : LocallyCompactSpace (Adeles F) :=
  adeles_locallyCompactSpace F

variable {m K : ℕ}

section Cosets

theorem rational_padGL' {k n : ℕ} (h : k ≤ n) (g : RationalGL F k) :
    AdelicGL.rational F n (padGL h g) = padGL h (AdelicGL.rational F k g) := by
  ext a b
  rw [padGL_apply, AdelicGL.rational_apply, padGL_apply]
  split_ifs <;> simp

theorem padRational_padGL' {k n r : ℕ} (h₁ : k ≤ n) (h₂ : n ≤ r + 1) (g : RationalGL F k) :
    padRational F h₂ (padGL h₁ g) = padRational F (h₁.trans h₂) g := by
  simp only [padRational, rational_padGL', padGL_comp]

omit [NumberField F] in
theorem topLeftMat_xcMat_apply (B : Fin K × Fin m → F) (c s : Fin (m + K)) :
    topLeftMat (xcMat m K B 0) c s =
      if hc : m ≤ (c : ℕ) then (if hs : (s : ℕ) < m then B (⟨(c : ℕ) - m, by omega⟩, ⟨s, hs⟩)
        else 0) else 0 := by
  simp only [topLeftMat, Matrix.submatrix_apply, xcMat, Fin.val_castSucc, Pi.zero_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

omit [NumberField F] in
/-- The entries of `diag(p, I) x̂_B` in `GL_(m+K)(F)`. -/
theorem rectRat_apply (p : RationalGL F m) (B : Fin K × Fin m → F) (r s : Fin (m + K)) :
    ((padGL (Nat.le_add_right m K) p * xcRat B : RationalGL F (m + K)) :
        Matrix (Fin (m + K)) (Fin (m + K)) F) r s =
      if hr : (r : ℕ) < m then (if hs : (s : ℕ) < m then
        (p : Matrix (Fin m) (Fin m) F) ⟨r, hr⟩ ⟨s, hs⟩ else 0)
      else (if hs : (s : ℕ) < m then B (⟨(r : ℕ) - m, by omega⟩, ⟨s, hs⟩)
        else (if r = s then 1 else 0)) := by
  rw [Units.val_mul, xcRat, sqZeroUnit_val, mul_add, mul_one, Matrix.add_apply, Matrix.mul_apply,
    Finset.sum_eq_single r]
  · rw [topLeftMat_xcMat_apply]
    simp only [padGL_apply]
    by_cases hr : (r : ℕ) < m
    · have h1 : ¬ m ≤ (r : ℕ) := by omega
      simp only [hr, h1, dite_true, dite_false, mul_zero, add_zero]
    · have h1 : m ≤ (r : ℕ) := by omega
      simp only [hr, h1, dite_true, dite_false, ite_true, one_mul]
      by_cases hs : (s : ℕ) < m
      · have hrs : r ≠ s := fun h => by subst h; exact hr hs
        simp only [hs, hrs, dite_true, ite_false, zero_add]
      · simp only [hs, dite_false, add_zero]
  · intro c _ hc
    rw [topLeftMat_xcMat_apply]
    simp only [padGL_apply]
    by_cases hc' : m ≤ (c : ℕ)
    · have hrc : r ≠ c := fun h => hc h.symm
      by_cases hr : (r : ℕ) < m
      · have : ¬ (c : ℕ) < m := by omega
        simp only [hr, this, dite_true, dite_false, zero_mul]
      · simp only [hr, hrc, dite_false, ite_false, zero_mul]
    · simp only [hc', dite_false, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `N(F) diag(p, I) x̂_B`, the coset attached to `(N(F) p, B)`. -/
def rectCoset (pB : UnipotentRationalCosets F m × (Fin K × Fin m → F)) :
    UnipotentRationalCosets F (m + K) :=
  Quotient.mk _ (padGL (Nat.le_add_right m K) pB.1.out * xcRat pB.2)

/-- `rectCoset` is injective. -/
theorem rectCoset_injective : Function.Injective (rectCoset (F := F) (m := m) (K := K)) := by
  rintro ⟨p₁, B₁⟩ ⟨p₂, B₂⟩ h
  have hr := QuotientGroup.rightRel_apply.mp (Quotient.exact h)
  obtain ⟨a₁, ha₁⟩ : ∃ a, a = padGL (Nat.le_add_right m K) p₁.out * xcRat (F := F) B₁ :=
    ⟨_, rfl⟩
  obtain ⟨a₂, ha₂⟩ : ∃ a, a = padGL (Nat.le_add_right m K) p₂.out * xcRat (F := F) B₂ :=
    ⟨_, rfl⟩
  obtain ⟨n, hn_def⟩ : ∃ n, n = a₂ * a₁⁻¹ := ⟨_, rfl⟩
  have hn : PrimitiveAdelicHeight.IsUnitriangular
      ((n : RationalGL F (m + K)) : Matrix (Fin (m + K)) (Fin (m + K)) F) := by
    rw [hn_def, ha₁, ha₂]
    exact (mem_rationalUpperUnipotent_iff F _).mp hr
  have heq : ∀ r s, (a₂ : Matrix (Fin (m + K)) (Fin (m + K)) F) r s =
      ∑ c, (n : Matrix (Fin (m + K)) (Fin (m + K)) F) r c *
        (a₁ : Matrix (Fin (m + K)) (Fin (m + K)) F) c s := by
    intro r s
    have : a₂ = n * a₁ := by rw [hn_def]; group
    conv_lhs => rw [this]
    rw [Units.val_mul, Matrix.mul_apply]
  -- the right columns of `n` are those of the identity
  have hcol : ∀ r s : Fin (m + K), ¬ (s : ℕ) < m →
      (n : Matrix (Fin (m + K)) (Fin (m + K)) F) r s = if r = s then 1 else 0 := by
    intro r s hs
    have h1 := heq r s
    rw [Finset.sum_eq_single s] at h1
    · rw [ha₁, ha₂, rectRat_apply, rectRat_apply] at h1
      simp only [hs, dite_false, ite_true, mul_one] at h1
      by_cases hr : (r : ℕ) < m
      · have hrs : r ≠ s := fun h => by subst h; exact hs hr
        simp only [hr, dite_true] at h1
        simp only [hrs, ↓reduceIte]
        exact h1.symm
      · simp only [hr, dite_false] at h1
        exact h1.symm
    · intro c _ hc
      rw [ha₁, rectRat_apply]
      by_cases hc' : (c : ℕ) < m
      · simp only [hc', hs, dite_true, dite_false, mul_zero]
      · simp only [hc', hs, dite_false, hc, ite_false, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- the rectangles agree
  have hB : B₁ = B₂ := by
    funext q
    obtain ⟨i, j⟩ := q
    obtain ⟨r, hr_def⟩ : ∃ r : Fin (m + K), (r : ℕ) = m + i := ⟨⟨m + i, by omega⟩, rfl⟩
    obtain ⟨s, hs_def⟩ : ∃ s : Fin (m + K), (s : ℕ) = j := ⟨⟨j, by omega⟩, rfl⟩
    have h1 := heq r s
    rw [Finset.sum_eq_single r] at h1
    · rw [ha₁, ha₂, rectRat_apply, rectRat_apply, hn.2 r, one_mul] at h1
      have hr : ¬ ((r : ℕ) < m) := by omega
      have hs : (s : ℕ) < m := by omega
      simp only [hr, hs, dite_true, dite_false] at h1
      have e : ((⟨(r : ℕ) - m, by omega⟩ : Fin K), (⟨(s : ℕ), hs⟩ : Fin m)) = (i, j) := by
        ext <;> simp <;> omega
      rw [e] at h1
      exact h1.symm
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with hlt | hgt
      · rw [hn.1 hlt, zero_mul]
      · have hc' : ¬ (c : ℕ) < m := by
          have : (r : ℕ) < c := hgt
          omega
        rw [hcol r c hc']
        simp only [Ne.symm hc, ↓reduceIte, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  subst hB
  have hpad : n = padGL (Nat.le_add_right m K) (p₂.out * p₁.out⁻¹) := by
    rw [hn_def, ha₁, ha₂, map_mul, map_inv]
    group
  rw [hpad] at hn
  have hu : PrimitiveAdelicHeight.IsUnitriangular
      ((p₂.out * p₁.out⁻¹ : RationalGL F m) : Matrix (Fin m) (Fin m) F) := by
    refine ⟨fun c d hcd => ?_, fun c => ?_⟩
    · have := hn.1 (show (Fin.castLE (Nat.le_add_right m K) d : Fin (m + K)) <
        Fin.castLE (Nat.le_add_right m K) c from hcd)
      rw [padGL_apply, dite_eq_left (by simp), dite_eq_left (by simp)] at this
      exact this
    · have := hn.2 (Fin.castLE (Nat.le_add_right m K) c)
      rw [padGL_apply, dite_eq_left (by simp), dite_eq_left (by simp)] at this
      exact this
  refine Prod.ext ?_ rfl
  rw [← Quotient.out_eq p₁, ← Quotient.out_eq p₂]
  apply Quotient.sound
  exact QuotientGroup.rightRel_apply.mpr ((mem_rationalUpperUnipotent_iff F _).mpr hu)

end Cosets

section Family

/-- The terms `W(diag(p, I) x̂_{X+B} y)` of the unfolded rectangular side, indexed by
`(N_m(F) p, B) ∈ N_m(F) \ GL_m(F) × F^{K×m}`. -/
def rectFamily (K : ℕ) (W : Points F (m + K + 1) → ℂ) (y : Points F (m + K + 1))
    (X : Fin K × Fin m → Adeles F) (pB : UnipotentRationalCosets F m × (Fin K × Fin m → F)) :
    ℂ :=
  W (padRational F (show m ≤ m + K + 1 by omega) pB.1.out *
    xcPoint F (X + fun q => algebraMap F (Adeles F) (pB.2 q)) 0 * y)

variable {ψ : AddChar (Adeles F) ℂ} (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1)
  {W : Points F (m + K + 1) → ℂ}

include hψF in
/-- The rectangular terms are corner terms along the injective coset map `rectCoset`. -/
theorem DualData.rectFamily_eq (hW : DualData F m ψ K W) (y : Points F (m + K + 1))
    (X : Fin K × Fin m → Adeles F) (pB : UnipotentRationalCosets F m × (Fin K × Fin m → F)) :
    rectFamily K W y X pB = cornerFamily F m K W (rectCoset pB) (xcPoint F X 0 * y) := by
  unfold rectFamily cornerFamily rectCoset
  have hab : QuotientGroup.rightRel (rationalUpperUnipotent F (m + K))
      (padGL (Nat.le_add_right m K) pB.1.out * xcRat pB.2)
      (Quotient.mk _ (padGL (Nat.le_add_right m K) pB.1.out * xcRat (F := F) pB.2) :
        UnipotentRationalCosets F (m + K)).out :=
    (QuotientGroup.rightRel _).iseqv.symm (Quotient.exact (Quotient.out_eq _))
  rw [hW.padRational_of_rightRel hψF _ hab]
  have hpt : padRational F (Nat.le_succ (m + K))
      (padGL (Nat.le_add_right m K) pB.1.out * xcRat pB.2) * (xcPoint F X 0 * y) =
      padRational F (show m ≤ m + K + 1 by omega) pB.1.out *
        xcPoint F (X + fun q => algebraMap F (Adeles F) (pB.2 q)) 0 * y := by
    rw [padRational_mul, padRational_padGL', ← xcPoint_rat_eq_padRational, ← mul_assoc,
      mul_assoc (padRational F _ _) (xcPoint F _ 0), xcPoint_mul,
      add_comm (fun q => algebraMap F (Adeles F) (pB.2 q)) X, add_zero]
  exact congrArg W hpt.symm

include hψF in
theorem DualData.locUnifSummable_rectFamily (hW : DualData F m ψ K W)
    (y : Points F (m + K + 1)) :
    LocUnifSummable (fun pB (X : Fin K × Fin m → Adeles F) => rectFamily K W y X pB) := by
  have hφ : Continuous fun X : Fin K × Fin m → Adeles F => xcPoint F (m := m) X 0 * y :=
    (continuous_xcPoint_left 0).mul continuous_const
  have h := (hW.summable.comp_injective rectCoset_injective).comp hφ
  have he : (fun pB (X : Fin K × Fin m → Adeles F) => rectFamily K W y X pB) =
      fun pB X => cornerFamily F m K W (rectCoset pB) (xcPoint F X 0 * y) := by
    funext pB X
    exact hW.rectFamily_eq hψF y X pB
  rw [he]
  exact h

include hψF in
theorem DualData.tsum_norm_rectFamily_le (hW : DualData F m ψ K W) (y : Points F (m + K + 1))
    (X : Fin K × Fin m → Adeles F) :
    ∑' pB, ‖rectFamily K W y X pB‖ ≤ cornerNormSum F m K W (xcPoint F X 0 * y) := by
  simp_rw [hW.rectFamily_eq hψF y X]
  exact tsum_comp_le_tsum_of_inj (hW.summable.1 _) (fun _ => norm_nonneg _) rectCoset_injective

include hψF in
theorem DualData.exists_rectFamily_bound [CompactSpace (AdeleQuotient F)]
    (hW : DualData F m ψ K W) (y : Points F (m + K + 1)) :
    ∃ C : ℝ, ∀ X : Fin K × Fin m → Adeles F, ∑' pB, ‖rectFamily K W y X pB‖ ≤ C := by
  obtain ⟨C, hC⟩ := hW.exists_bound hψF y
  refine ⟨C, fun X => (hW.tsum_norm_rectFamily_le hψF y X).trans ?_⟩
  have := hC X 0 1
  rwa [OneMemClass.coe_one, midPoint_one, mul_one] at this

include hψF in
theorem DualData.continuous_tsum_rectFamily (hW : DualData F m ψ K W)
    (y : Points F (m + K + 1)) :
    Continuous fun X : Fin K × Fin m → Adeles F => ∑' pB, rectFamily K W y X pB := by
  refine (hW.locUnifSummable_rectFamily hψF y).continuous_tsum fun pB => ?_
  have h1 : Continuous fun X : Fin K × Fin m → Adeles F =>
      xcPoint F (m := m) (X + fun q => algebraMap F (Adeles F) (pB.2 q)) 0 :=
    (continuous_xcPoint_left 0).comp (continuous_id.add continuous_const)
  exact hW.continuous.comp ((continuous_const.mul h1).mul continuous_const)

theorem isPeriodic_tsum_rectFamily (y : Points F (m + K + 1)) :
    IsPeriodic fun X : Fin K × Fin m → Adeles F => ∑' pB, rectFamily K W y X pB := by
  intro X ρ
  show ∑' pB, rectFamily K W y (X + ratVec ρ) pB = ∑' pB, rectFamily K W y X pB
  have h : ∀ pB, rectFamily K W y (X + ratVec ρ) pB =
      rectFamily K W y X ((Equiv.prodCongr (Equiv.refl _) (Equiv.addLeft ρ)) pB) := by
    intro pB
    unfold rectFamily
    have e : (X + ratVec ρ + fun q => algebraMap F (Adeles F) (pB.2 q)) =
        X + fun q => algebraMap F (Adeles F)
          (((Equiv.prodCongr (Equiv.refl _) (Equiv.addLeft ρ)) pB).2 q) := by
      funext q
      simp [ratVec, add_assoc]
    rw [e]
    rfl
  rw [tsum_congr h]
  exact (Equiv.prodCongr (Equiv.refl _) (Equiv.addLeft ρ)).tsum_eq
    (fun pB => rectFamily K W y X pB)

end Family

section RectStep

/-- Splitting a rational rectangle on `K + 1` rows into its first `K` rows and its last row. -/
def joinRectEquiv : (Fin K × Fin m → F) × (Fin m → F) ≃ (Fin (K + 1) × Fin m → F) where
  toFun p := joinRect p.1 p.2
  invFun B := (fun q => B (q.1.castSucc, q.2), fun j => B (Fin.last K, j))
  left_inv p := by
    obtain ⟨x, b⟩ := p
    ext q
    · simp [joinRect, rectSplit]
    · simp [joinRect, rectSplit]
  right_inv B := by
    funext k
    obtain ⟨i, j⟩ := k
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · simp [joinRect, rectSplit]
    · simp [joinRect, rectSplit]

/-- The reindexing `(β, (p, β')) ↦ (p, (β', β))` of the rectangular sum. -/
def rectSplitEquiv : (Fin m → F) × (UnipotentRationalCosets F m × (Fin K × Fin m → F)) ≃
    UnipotentRationalCosets F m × (Fin (K + 1) × Fin m → F) :=
  (Equiv.prodComm _ _).trans ((Equiv.prodAssoc _ _ _).trans
    (Equiv.prodCongr (Equiv.refl _) joinRectEquiv))

theorem rectFamily_succ (W : Points F (m + (K + 1) + 1) → ℂ) (y : Points F (m + (K + 1) + 1))
    (x' : Fin K × Fin m → Adeles F) (b : Fin m → Adeles F) (β : Fin m → F)
    (pB : UnipotentRationalCosets F m × (Fin K × Fin m → F)) :
    rectFamily (K + 1) W y (joinRect x' b) (rectSplitEquiv (β, pB)) =
      rectFamily K (dualPullback W y) (rowPoint F (b + fun j => algebraMap F (Adeles F) (β j)))
        x' pB := by
  obtain ⟨p, β'⟩ := pB
  unfold rectFamily dualPullback
  have e1 : (joinRect x' b + fun q => algebraMap F (Adeles F)
      ((rectSplitEquiv (F := F) (β, (p, β'))).2 q)) =
      joinRect (x' + fun q => algebraMap F (Adeles F) (β' q))
        (b + fun j => algebraMap F (Adeles F) (β j)) := by
    funext k
    simp only [rectSplitEquiv, Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
      Equiv.prodAssoc_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq,
      joinRectEquiv, Equiv.coe_fn_mk, joinRect, Pi.add_apply]
    cases rectSplit.symm k <;> rfl
  have hpt : padRational F (show m ≤ m + (K + 1) + 1 by omega)
      ((rectSplitEquiv (F := F) (β, (p, β'))).1).out *
        xcPoint F (joinRect x' b + fun q => algebraMap F (Adeles F)
          ((rectSplitEquiv (F := F) (β, (p, β'))).2 q)) 0 * y =
      pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega)
        (padRational F (show m ≤ m + K + 1 by omega) p.out *
          xcPoint F (x' + fun q => algebraMap F (Adeles F) (β' q)) 0 *
            rowPoint F (b + fun j => algebraMap F (Adeles F) (β j))) * y := by
    rw [e1, xcPoint_succ_rect, restOfRect_joinRect, rowOfRect_joinRect]
    simp only [pad_mul, pad_padRational, mul_assoc]
    rfl
  exact congrArg W hpt

end RectStep

section Induction

variable [CompactSpace (AdeleQuotient F)]

/-- The unfolded rectangular side as a torus integral of the sum over
`(N_m(F) p, B) ∈ N_m(F) \ GL_m(F) × F^{K×m}`. -/
def dualRectT (K : ℕ) (W : Points F (m + K + 1) → ℂ) (y : Points F (m + K + 1)) : ℂ :=
  Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K × Fin m) fun X =>
    ∑' pB, rectFamily K W y X pB

variable {ψ : AddChar (Adeles F) ℂ} (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1)

include hψF in
/-- **The rank step of the rectangular side**. -/
theorem DualData.dualRectT_succ {W : Points F (m + (K + 1) + 1) → ℂ}
    (hW : DualData F m ψ (K + 1) W) (y : Points F (m + (K + 1) + 1)) :
    dualRectT (K + 1) W y =
      Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin m) fun b =>
        ∑' β : Fin m → F, dualRectT K (dualPullback W y)
          (rowPoint F (b + fun j => algebraMap F (Adeles F) (β j))) := by
  have hV := hW.pullbackData hψF y
  obtain ⟨C, hC⟩ := hW.exists_rectFamily_bound hψF y
  rw [dualRectT, torusIntegral_rect_succ (isPeriodic_tsum_rectFamily y)
    (hW.continuous_tsum_rectFamily hψF y)]
  refine Langlands.Automorphic.CuspidalWhittaker.torusIntegral_congr fun b => ?_
  have hfam : ∀ x' : Fin K × Fin m → Adeles F, Summable fun z =>
      ‖rectFamily (K + 1) W y (joinRect x' b) (rectSplitEquiv z)‖ := fun x' =>
    ((rectSplitEquiv (F := F) (m := m) (K := K)).summable_iff
      (f := fun pB => ‖rectFamily (K + 1) W y (joinRect x' b) pB‖)).mpr
      ((hW.locUnifSummable_rectFamily hψF y).1 _)
  have hinner : ∀ x' : Fin K × Fin m → Adeles F,
      ∑' pB, rectFamily (K + 1) W y (joinRect x' b) pB =
        ∑' β : Fin m → F, ∑' pB', rectFamily K (dualPullback W y)
          (rowPoint F (b + fun j => algebraMap F (Adeles F) (β j))) x' pB' := by
    intro x'
    have hs : Summable fun z => rectFamily (K + 1) W y (joinRect x' b) (rectSplitEquiv z) :=
      (hfam x').of_norm
    rw [← (rectSplitEquiv (F := F) (m := m) (K := K)).tsum_eq,
      hs.tsum_prod' (fun β => hs.prod_factor β)]
    exact tsum_congr fun β => tsum_congr fun pB => rectFamily_succ W y x' b β pB
  rw [Langlands.Automorphic.CuspidalWhittaker.torusIntegral_congr hinner]
  have hterm : ∀ (x' : Fin K × Fin m → Adeles F) (β : Fin m → F),
      ‖∑' pB', rectFamily K (dualPullback W y)
        (rowPoint F (b + fun j => algebraMap F (Adeles F) (β j))) x' pB'‖ ≤
      ∑' pB', ‖rectFamily (K + 1) W y (joinRect x' b) (rectSplitEquiv (β, pB'))‖ := by
    intro x' β
    simp_rw [← rectFamily_succ W y x' b β]
    exact norm_tsum_le_tsum_norm ((hfam x').prod_factor β)
  have hsumG : ∀ x' : Fin K × Fin m → Adeles F, Summable fun β : Fin m → F =>
      ∑' pB', ‖rectFamily (K + 1) W y (joinRect x' b) (rectSplitEquiv (β, pB'))‖ :=
    fun x' => (hfam x').prod
  have hGle : ∀ x' : Fin K × Fin m → Adeles F, ∑' β : Fin m → F,
      ∑' pB', ‖rectFamily (K + 1) W y (joinRect x' b) (rectSplitEquiv (β, pB'))‖ ≤ C := by
    intro x'
    rw [← (hfam x').tsum_prod' (fun β => (hfam x').prod_factor β),
      (rectSplitEquiv (F := F) (m := m) (K := K)).tsum_eq
        (fun pB => ‖rectFamily (K + 1) W y (joinRect x' b) pB‖)]
    exact hC _
  have hs : ∀ x' : Fin K × Fin m → Adeles F, Summable fun β : Fin m → F =>
      ‖∑' pB', rectFamily K (dualPullback W y)
        (rowPoint F (b + fun j => algebraMap F (Adeles F) (β j))) x' pB'‖ :=
    fun x' => Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hterm x') (hsumG x')
  rw [torusIntegral_tsum
    (f := fun (β : Fin m → F) (x' : Fin K × Fin m → Adeles F) => ∑' pB', rectFamily K
      (dualPullback W y) (rowPoint F (b + fun j => algebraMap F (Adeles F) (β j))) x' pB')
    (fun β => hV.continuous_tsum_rectFamily hψF _) (fun β => isPeriodic_tsum_rectFamily _) hs
    (fun x' => (Summable.tsum_le_tsum (hterm x') (hs x') (hsumG x')).trans (hGle x'))]
  rfl

/-- The rectangular side at `K = 0` is the corner sum. -/
theorem dualRectT_zero (W : Points F (m + 0 + 1) → ℂ) (y : Points F (m + 0 + 1)) :
    dualRectT 0 W y = cornerSum F m 0 W y := by
  rw [dualRectT, torusIntegral_of_isEmpty]
  unfold cornerSum cornerFamily rectFamily
  have hx : ∀ B : Fin 0 × Fin m → F, xcPoint F (m := m) (K := 0)
      ((0 : Fin 0 × Fin m → Adeles F) + fun q => algebraMap F (Adeles F) (B q)) 0 = 1 := by
    intro B
    have : ((0 : Fin 0 × Fin m → Adeles F) + fun q => algebraMap F (Adeles F) (B q)) = 0 :=
      funext fun q => q.1.elim0
    rw [this, xcPoint_zero]
  simp_rw [hx, mul_one]
  exact (Equiv.prodUnique _ _).tsum_eq
    (fun p : UnipotentRationalCosets F m => W (padRational F (Nat.le_succ (m + 0)) p.out * y))

/-- The dual period at `K = 0` is the corner sum. -/
theorem dualPeriod_zero (ψ : AddChar (Adeles F) ℂ) (W : Points F (m + 0 + 1) → ℂ)
    (y : Points F (m + 0 + 1)) :
    dualPeriod F m 0 ψ W y = cornerSum F m 0 W y := by
  have hsub : ∀ u : unipotentAdelic F 0, u = 1 := by
    intro u
    apply Subtype.ext
    apply (GeneralLinearGroupPoints.adelicEquiv F 0).injective
    apply Units.ext
    ext i
    exact i.elim0
  have hf : (fun u : unipotentAdelic F 0 => ψ (superSum F (u : Points F 0)) *
      rectPeriod F m 0 ψ (cornerSum F m 0 W) (midPoint F (u : Points F 0) * y)) =
      fun _ => cornerSum F m 0 W y := by
    funext u
    rw [hsub u, OneMemClass.coe_one, midPoint_one, one_mul]
    unfold rectPeriod
    rw [torusIntegral_of_isEmpty, torusIntegral_of_isEmpty, xcPoint_zero, one_mul]
    simp [superSum, lastEntry]
  unfold dualPeriod unipotentPeriod
  rw [hf, setIntegral_const, smul_smul, measureReal_def, inv_mul_cancel₀ (right_ne_zero_of_mul_eq_one
    (quotientMassNormalizer_mul_haar F 0)), one_smul]

variable (ψ) in
include hψF in
/-- **The dual period equals the unfolded rectangular side**, for every dual Whittaker-type
function at every rank. -/
theorem dualPeriod_eq_dualRectT (hψc : Continuous ψ) (hψ1 : ∀ x, ‖ψ x‖ = 1)
    (hψn : ∀ a : F, a ≠ 0 → ∃ y : Adeles F, ψ (algebraMap F (Adeles F) a * y) ≠ 1) :
    ∀ (K : ℕ) (W : Points F (m + K + 1) → ℂ), DualData F m ψ K W →
      ∀ y : Points F (m + K + 1), dualPeriod F m K ψ W y = dualRectT K W y
  | 0, W, _, y => by rw [dualPeriod_zero, dualRectT_zero]
  | K + 1, W, hW, y => by
    rw [hW.dualPeriod_succ hψF hψc hψ1 hψn y, hW.dualRectT_succ hψF y]
    refine Langlands.Automorphic.CuspidalWhittaker.torusIntegral_congr fun b => ?_
    refine tsum_congr fun β => ?_
    exact dualPeriod_eq_dualRectT hψc hψ1 hψn K _ (hW.pullbackData hψF y) _

end Induction

end Langlands.Global.RankinSelbergGlobal.Unfolding
