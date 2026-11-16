import Langlands.Global.RankinSelberg.WhittakerExpansionCore.ColumnTorus
import Langlands.Global.RankinSelberg.WhittakerExpansionCore.ColumnsB
import Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerCosets
import Langlands.Global.RankinSelberg.EqualAnalyticCharacter

/-! # The Whittaker sums along a column

For `j ≤ r + 1` let `G_j(x) = Σ_{q ∈ N_j(F) \ GL_j(F)} W_f(diag(q, I) x)`. Along column `j + 1`
the terms of `G_(j+1)` are characters times constants:
`W_f(diag(q, I) u(y) x) = ψ₀(b ξ_q · y) W_f(diag(q, I) x)` with `ξ_q` the last row of `q` and
`ψ = ψ₀(b ·)`. Hence, for absolutely summable terms, the Fourier coefficient of `G_(j+1)` along
the column at `a₀` is the sum of the terms with `b ξ_q = a₀`. This gives the properties of
`G_(j+1)` used in the uniqueness step: continuity and periodicity along the column, invariance
under rational block matrices of size `j + 1`, vanishing of the zeroth coefficient, and the
coefficient at `ψ₀(b y_j)` equal to `G_j`. -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ComplexConjugate
set_option autoImplicit false

namespace Langlands.Automorphic.CuspidalWhittaker

open Langlands.Global

variable {K : Type u} [Field K] [NumberField K]

section Series

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

omit [DecidableEq Idx] in
theorem continuous_pairingCharacter_lift (a : Idx → K) :
    Continuous (fun t : Idx → AdeleQuotient K => pairingCharacter a (torusLift t)) :=
  (isPeriodic_pairingCharacter a).continuous_lift (continuous_pairingCharacter a)

omit [DecidableEq Idx] in
theorem continuous_tsum_pairingCharacter {Q : Type*} (a : Q → Idx → K) (w : Q → ℂ)
    (hw : Summable fun q => ‖w q‖) :
    Continuous (fun y : Idx → Adeles K => ∑' q, pairingCharacter (a q) y * w q) :=
  continuous_tsum (fun q => (continuous_pairingCharacter (a q)).mul continuous_const) hw
    (fun q y => by rw [norm_mul, norm_pairingCharacter, one_mul])

omit [DecidableEq Idx] in
theorem isPeriodic_tsum_pairingCharacter {Q : Type*} (a : Q → Idx → K) (w : Q → ℂ) :
    IsPeriodic (fun y : Idx → Adeles K => ∑' q, pairingCharacter (a q) y * w q) := by
  intro y k
  refine tsum_congr fun q => ?_
  rw [isPeriodic_pairingCharacter (a q) y k]

variable [CompactSpace (AdeleQuotient K)]

open scoped Classical in
/-- Orthogonality of two characters on the torus. -/
theorem torusIntegral_pairingCharacter_mul_conj (a a₀ : Idx → K) :
    torusIntegral Idx (fun y => pairingCharacter a y * conj (pairingCharacter a₀ y)) =
      if a = a₀ then 1 else 0 := by
  have h : ∀ y, pairingCharacter a y * conj (pairingCharacter a₀ y) =
      pairingCharacter (a - a₀) y := by
    intro y
    rw [← pairingCharacter_neg, ← pairingCharacter_add_left, sub_eq_add_neg]
  rw [torusIntegral_congr h]
  by_cases ha : a = a₀
  · rw [ite_eq_left ha, ha, sub_self]
    exact (torusIntegral_congr fun y => pairingCharacter_zero y).trans (torusIntegral_const 1)
  · rw [ite_eq_right ha]
    exact Langlands.Global.RankinSelbergGlobal.Unfolding.torusIntegral_pairingCharacter
      (sub_ne_zero.mpr ha)

open scoped Classical in
/-- **Fourier coefficients of an absolutely convergent character series.** -/
theorem fourierCoeff_tsum_pairingCharacter {Q : Type*} [Countable Q] (a : Q → Idx → K)
    (w : Q → ℂ) (hw : Summable fun q => ‖w q‖) (a₀ : Idx → K) :
    fourierCoeff (fun y => ∑' q, pairingCharacter (a q) y * w q) a₀ =
      ∑' q, if a q = a₀ then w q else 0 := by
  unfold fourierCoeff torusIntegral
  have hc : ∀ q, Continuous (fun t : Idx → AdeleQuotient K =>
      pairingCharacter (a q) (torusLift t) * w q * conj (pairingCharacter a₀ (torusLift t))) :=
    fun q => ((continuous_pairingCharacter_lift (a q)).mul continuous_const).mul
      (Complex.continuous_conj.comp (continuous_pairingCharacter_lift a₀))
  have hnorm : ∀ q (t : Idx → AdeleQuotient K), ‖pairingCharacter (a q) (torusLift t) * w q *
      conj (pairingCharacter a₀ (torusLift t))‖ = ‖w q‖ := by
    intro q t
    rw [norm_mul, norm_mul, Complex.norm_conj, norm_pairingCharacter, norm_pairingCharacter,
      one_mul, mul_one]
  have h1 : ∀ t : Idx → AdeleQuotient K,
      (∑' q, pairingCharacter (a q) (torusLift t) * w q) *
        conj (pairingCharacter a₀ (torusLift t)) =
      ∑' q, pairingCharacter (a q) (torusLift t) * w q *
        conj (pairingCharacter a₀ (torusLift t)) := fun t => tsum_mul_right.symm
  simp_rw [h1]
  rw [← integral_tsum_of_summable_integral_norm (fun q => integrable_of_continuous (hc q))
    (by simp_rw [hnorm, integral_const, probReal_univ, one_smul]; exact hw)]
  refine tsum_congr fun q => ?_
  have h2 : ∀ t : Idx → AdeleQuotient K, pairingCharacter (a q) (torusLift t) * w q *
      conj (pairingCharacter a₀ (torusLift t)) = w q * (pairingCharacter (a q) (torusLift t) *
      conj (pairingCharacter a₀ (torusLift t))) := fun t => by ring
  simp_rw [h2]
  rw [integral_const_mul]
  have h3 : ∫ t, pairingCharacter (a q) (torusLift t) * conj (pairingCharacter a₀ (torusLift t))
      ∂torusHaar K Idx = if a q = a₀ then 1 else 0 :=
    torusIntegral_pairingCharacter_mul_conj (a q) a₀
  rw [h3]
  by_cases hq : a q = a₀
  · rw [ite_eq_left hq, ite_eq_left hq, mul_one]
  · rw [ite_eq_right hq, ite_eq_right hq, mul_zero]

end Series

section Block

variable {R : Type*} [CommRing R] {n k : ℕ}

/-- The upper left `k × k` block of a square matrix. -/
def topBlock (hk : k ≤ n) (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin k) (Fin k) R :=
  Matrix.of fun a b => M (Fin.castLE hk a) (Fin.castLE hk b)

theorem topBlock_mul (hk : k ≤ n) {M : Matrix (Fin n) (Fin n) R} (hM : IsBlk k M)
    (N : Matrix (Fin n) (Fin n) R) :
    topBlock hk (M * N) = topBlock hk M * topBlock hk N := by
  ext a b
  simp only [topBlock, Matrix.of_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _ ?_
    (fun c => rfl)
  intro c hc
  have hck : k ≤ (c : ℕ) := by
    by_contra h
    exact hc ⟨⟨c, by omega⟩, rfl⟩
  rw [hM _ c (Or.inr hck), Matrix.one_apply_ne, zero_mul]
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_castLE] at this
  omega

theorem topBlock_one (hk : k ≤ n) : topBlock hk (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext a b
  simp only [topBlock, Matrix.of_apply, Matrix.one_apply, Fin.castLE_inj]

/-- The upper left block of an invertible block matrix, as an invertible matrix. -/
def topBlockGL (hk : k ≤ n) (g : GL (Fin n) R) (hg : IsBlk k g.val) : GL (Fin k) R where
  val := topBlock hk g.val
  inv := topBlock hk (g⁻¹).val
  val_inv := by
    rw [← topBlock_mul hk hg, ← Units.val_mul, mul_inv_cancel, Units.val_one, topBlock_one]
  inv_val := by
    rw [← topBlock_mul hk hg.inv, ← Units.val_mul, inv_mul_cancel, Units.val_one, topBlock_one]

theorem padGL_topBlockGL (hk : k ≤ n) (g : GL (Fin n) R) (hg : IsBlk k g.val) :
    RankinSelbergGlobal.padGL hk (topBlockGL hk g hg) = g := by
  apply Units.ext
  ext a b
  rw [RankinSelbergGlobal.UnequalAnalytic.padGL_apply]
  by_cases h : (a : ℕ) < k ∧ (b : ℕ) < k
  · rw [dite_eq_left h]
    rfl
  · rw [dite_eq_right h]
    refine (hg a b ?_).symm
    by_contra hh
    push Not at hh
    exact h ⟨hh.1, hh.2⟩

end Block

end Langlands.Automorphic.CuspidalWhittaker

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints Langlands.Automorphic.CuspidalWhittaker

local instance gSideSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance gSideSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

section Cosets

/-- Right multiplication of cosets, `N_k(F) g ↦ N_k(F) g A`. -/
def cosetMulRight {k : ℕ} (A : RationalGL F k) :
    UnipotentRationalCosets F k ≃ UnipotentRationalCosets F k where
  toFun := Quotient.map' (· * A) fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using hab
  invFun := Quotient.map' (· * A⁻¹) fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left] using hab
  left_inv q := by
    induction q using Quotient.inductionOn with | h a => ?_
    change Quotient.mk _ (a * A * A⁻¹) = Quotient.mk _ a
    rw [mul_inv_cancel_right]
  right_inv q := by
    induction q using Quotient.inductionOn with | h a => ?_
    change Quotient.mk _ (a * A⁻¹ * A) = Quotient.mk _ a
    rw [inv_mul_cancel_right]

omit [NumberField F] in
theorem rightRel_cosetMulRight {k : ℕ} (A : RationalGL F k) (q : UnipotentRationalCosets F k) :
    QuotientGroup.rightRel (rationalUpperUnipotent F k) (q.out * A) (cosetMulRight F A q).out := by
  have h : (Quotient.mk _ (q.out * A) : UnipotentRationalCosets F k) =
      Quotient.mk _ (cosetMulRight F A q).out := by
    rw [Quotient.out_eq]
    conv_rhs => rw [← Quotient.out_eq q]
    rfl
  exact Quotient.exact h

end Cosets

section Sum

variable {r : ℕ} (ψ : AddChar (Adeles F) ℂ) (f : Points F (r + 1) → ℂ)

/-- The Whittaker sum at level `j`: `G_j(x) = Σ_{q ∈ N_j(F) \ GL_j(F)} W_f(diag(q, I) x)`. -/
def whittakerSum (j : ℕ) (hj : j ≤ r + 1) (x : Points F (r + 1)) : ℂ :=
  ∑' q : UnipotentRationalCosets F j, whittaker F r ψ f (padRational F hj q.out * x)

/-- The Whittaker sum as a function on `GL_(r+1)(𝔸)` in matrix coordinates. -/
def whittakerSumGL (j : ℕ) (hj : j ≤ r + 1) (g : AdelicGL F (r + 1)) : ℂ :=
  whittakerSum F ψ f j hj ((GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm g)

/-- The character of the last row of `q`, scaled by `b`, as a vector of length `r + 1`. -/
def rowChar {j : ℕ} (b : F) (q : UnipotentRationalCosets F (j + 1)) : Fin (r + 1) → F :=
  fun a => if h : (a : ℕ) < j + 1 then
    b * (q.out : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j) ⟨a, h⟩ else 0

omit [NumberField F] in
theorem rowChar_castLE {j : ℕ} (b : F) (q : UnipotentRationalCosets F (j + 1))
    (hj : j + 1 ≤ r + 1) (c : Fin (j + 1)) :
    rowChar F (r := r) b q (Fin.castLE hj c) =
      b * (q.out : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j) c := by
  simp only [rowChar]
  rw [dite_eq_left (by rw [Fin.val_castLE]; exact c.isLt)]
  rfl

omit [NumberField F] in
theorem rowChar_ne_zero {j : ℕ} {b : F} (hb : b ≠ 0) (q : UnipotentRationalCosets F (j + 1))
    (hj : j + 1 ≤ r + 1) : rowChar F (r := r) b q ≠ 0 := by
  intro h
  apply lastRow_ne_zero q.out
  funext c
  have h1 := congrFun h (Fin.castLE hj c)
  rw [rowChar_castLE, Pi.zero_apply] at h1
  exact (mul_eq_zero.mp h1).resolve_left hb

theorem castLE_eq_charIdx_iff {j : ℕ} (hj : j < r) (c : Fin (j + 1)) :
    (Fin.castLE (by omega : j + 1 ≤ r + 1) c : Fin (r + 1)) = charIdx j hj ↔ c = Fin.last j := by
  constructor
  · intro e
    apply Fin.ext
    have := congrArg Fin.val e
    rw [Fin.val_castLE, charIdx_val] at this
    rw [this, Fin.val_last]
  · intro e
    apply Fin.ext
    rw [Fin.val_castLE, charIdx_val, e, Fin.val_last]

omit [NumberField F] in
theorem rowChar_eq_single_iff {j : ℕ} (hj : j < r) {b : F} (hb : b ≠ 0)
    (q : UnipotentRationalCosets F (j + 1)) :
    rowChar F b q = Pi.single (charIdx j hj) b ↔ LastRowStandard F q.out := by
  constructor
  · intro h c
    have h1 := congrFun h (Fin.castLE (by omega) c)
    rw [rowChar_castLE, Pi.single_apply] at h1
    rw [Matrix.one_apply]
    by_cases hc : c = Fin.last j
    · rw [ite_eq_left ((castLE_eq_charIdx_iff hj c).mpr hc)] at h1
      rw [ite_eq_left hc.symm]
      exact mul_left_cancel₀ hb (h1.trans (mul_one b).symm)
    · rw [ite_eq_right (fun e => hc ((castLE_eq_charIdx_iff hj c).mp e))] at h1
      rw [ite_eq_right (fun e => hc e.symm)]
      exact (mul_eq_zero.mp h1).resolve_left hb
  · intro h
    funext a
    by_cases ha : (a : ℕ) < j + 1
    · have key : ∀ c : Fin (j + 1), rowChar F b q (Fin.castLE (by omega : j + 1 ≤ r + 1) c) =
          (Pi.single (charIdx j hj) b : Fin (r + 1) → F)
            (Fin.castLE (by omega : j + 1 ≤ r + 1) c) := by
        intro c
        rw [rowChar_castLE, h c, Pi.single_apply, Matrix.one_apply]
        by_cases hc : c = Fin.last j
        · rw [ite_eq_left hc.symm, ite_eq_left ((castLE_eq_charIdx_iff hj c).mpr hc), mul_one]
        · rw [ite_eq_right (fun e => hc e.symm),
            ite_eq_right (fun e => hc ((castLE_eq_charIdx_iff hj c).mp e)), mul_zero]
      exact key ⟨a, ha⟩
    · simp only [rowChar]
      rw [dite_eq_right ha]
      have e1 : a ≠ charIdx j hj := fun e => ha (by rw [e, charIdx_val]; omega)
      rw [Pi.single_eq_of_ne e1]

theorem symm_colUnit_mul {j : ℕ} (hj : j < r) (y : Fin (r + 1) → Adeles F)
    (g : AdelicGL F (r + 1)) :
    (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm (colUnit (colIdx j hj) y * g) =
      colPoint F (j := j) y * (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm g := by
  rw [map_mul, ← colPoint_eq_symm_colUnit F hj]

theorem symm_rational_mul_of_isBlk {k : ℕ} (hk : k ≤ r + 1) (β : RationalGL F (r + 1))
    (hβ : IsBlk k β.val) (g : AdelicGL F (r + 1)) :
    (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm
        (AdelicGL.rational F (r + 1) β * g) =
      padRational F hk (topBlockGL hk β hβ) *
        (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm g := by
  rw [map_mul]
  congr 1
  rw [padRational, padGL_rational, padGL_topBlockGL]
  rfl

section Invariance

variable (hψ : IsStandardAdditiveCharacter F ψ)
  (hfΓ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x, f (k * x) = f x)

include hψ hfΓ

/-- The terms of `G_(j+1)` along column `j + 1`. -/
theorem whittaker_padRational_colPoint_eq {b : F}
    (hb : ∀ x, ψ x = EqualAnalytic.standardCharacter F (algebraMap F (Adeles F) b * x))
    {j : ℕ} (hj : j < r) (q : UnipotentRationalCosets F (j + 1)) (y : Fin (r + 1) → Adeles F)
    (x : Points F (r + 1)) :
    whittaker F r ψ f
        (padRational F (by omega : j + 1 ≤ r + 1) q.out * (colPoint F (j := j) y * x)) =
      pairingCharacter (rowChar F b q) y *
        whittaker F r ψ f (padRational F (by omega : j + 1 ≤ r + 1) q.out * x) := by
  have hc : IsColSupported j (truncVec (j + 1) y) := fun a ha => by
    simp only [truncVec]
    exact ite_eq_right (by omega)
  rw [← colPoint_truncVec F (j := j) y,
    whittaker_padRational_colPoint F ψ hψ f hfΓ hj q.out _ hc x]
  congr 1
  rw [hb, EqualAnalytic.standardCharacter_apply, pairingCharacter, Finset.mul_sum]
  congr 2
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [rowChar, truncVec]
  by_cases ha : (a : ℕ) < j + 1
  · rw [dite_eq_left ha, dite_eq_left ha, ite_eq_left ha, map_mul, mul_assoc]
  · rw [dite_eq_right ha, dite_eq_right ha, ite_eq_right ha, map_zero, zero_mul, zero_mul,
      mul_zero]

/-- `W_f(diag((cosetPad q).out, I) x) = W_f(diag(q.out, I) x)`. -/
theorem whittaker_padRational_cosetPad {j : ℕ} (hj : j + 1 ≤ r + 1)
    (q : UnipotentRationalCosets F j) (x : Points F (r + 1)) :
    whittaker F r ψ f (padRational F hj (cosetPad F j q).out * x) =
      whittaker F r ψ f (padRational F (by omega : j ≤ r + 1) q.out * x) := by
  induction q using Quotient.inductionOn with | h a => ?_
  have h1 : QuotientGroup.rightRel (rationalUpperUnipotent F (j + 1))
      (padGL (Nat.le_succ j) a) (cosetPad F j (Quotient.mk _ a)).out := by
    rw [cosetPad_mk]
    exact Quotient.exact (Quotient.out_eq _).symm
  have h2 : QuotientGroup.rightRel (rationalUpperUnipotent F j) a
      (Quotient.mk _ a : UnipotentRationalCosets F j).out :=
    Quotient.exact (Quotient.out_eq _).symm
  rw [whittaker_padRational_of_rightRel F ψ hψ f hfΓ _ h1, padRational_padGL,
    whittaker_padRational_of_rightRel F ψ hψ f hfΓ _ h2]

/-- `G_k` is left invariant under `diag(A, I)` for `A ∈ GL_k(F)`. -/
theorem whittakerSum_padRational_mul {k : ℕ} (hk : k ≤ r + 1) (A : RationalGL F k)
    (x : Points F (r + 1)) :
    whittakerSum F ψ f k hk (padRational F hk A * x) = whittakerSum F ψ f k hk x := by
  unfold whittakerSum
  have h : ∀ q : UnipotentRationalCosets F k,
      whittaker F r ψ f (padRational F hk q.out * (padRational F hk A * x)) =
        whittaker F r ψ f (padRational F hk (cosetMulRight F A q).out * x) := by
    intro q
    rw [← mul_assoc, ← padRational_mul,
      whittaker_padRational_of_rightRel F ψ hψ f hfΓ hk (rightRel_cosetMulRight F A q)]
  rw [tsum_congr h]
  exact (cosetMulRight F A).tsum_eq
    (fun q : UnipotentRationalCosets F k => whittaker F r ψ f (padRational F hk q.out * x))

/-- `G̃_k` is left invariant under rational block matrices of size `k`. -/
theorem whittakerSumGL_rational_mul {k : ℕ} (hk : k ≤ r + 1) (β : RationalGL F (r + 1))
    (hβ : IsBlk k β.val) (g : AdelicGL F (r + 1)) :
    whittakerSumGL F ψ f k hk (AdelicGL.rational F (r + 1) β * g) =
      whittakerSumGL F ψ f k hk g := by
  unfold whittakerSumGL
  rw [symm_rational_mul_of_isBlk F hk β hβ g]
  exact whittakerSum_padRational_mul F ψ f hψ hfΓ hk _ _

omit hψ hfΓ in
/-- `G_0 = W_f`. -/
theorem whittakerSum_zero (x : Points F (r + 1)) :
    whittakerSum F ψ f 0 (Nat.zero_le _) x = whittaker F r ψ f x := by
  have hsub : ∀ g : RationalGL F 0, g = 1 := fun g =>
    Units.ext (Matrix.ext fun i _ => i.elim0)
  have hq : ∀ q : UnipotentRationalCosets F 0, q = Quotient.mk _ 1 := fun q => by
    rw [← Quotient.out_eq q, hsub q.out]
  rw [whittakerSum, tsum_eq_single (Quotient.mk _ 1) (fun q hq' => absurd (hq q) hq'),
    hsub (Quotient.mk _ 1 : UnipotentRationalCosets F 0).out]
  simp only [padRational, map_one, one_mul]

section Column

variable {b : F} (hb : ∀ x, ψ x = EqualAnalytic.standardCharacter F (algebraMap F (Adeles F) b * x))
  {j : ℕ} (hj : j < r)
  (hsum : ∀ x : Points F (r + 1), Summable fun q : UnipotentRationalCosets F (j + 1) =>
    ‖whittaker F r ψ f (padRational F (by omega : j + 1 ≤ r + 1) q.out * x)‖)

include hb

theorem whittakerSumGL_colUnit_mul (y : Fin (r + 1) → Adeles F) (g : AdelicGL F (r + 1)) :
    whittakerSumGL F ψ f (j + 1) (by omega) (colUnit (colIdx j hj) y * g) =
      ∑' q : UnipotentRationalCosets F (j + 1), pairingCharacter (rowChar F b q) y *
        whittaker F r ψ f (padRational F (by omega : j + 1 ≤ r + 1) q.out *
          (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm g) := by
  unfold whittakerSumGL whittakerSum
  rw [symm_colUnit_mul F hj]
  exact tsum_congr fun q => whittaker_padRational_colPoint_eq F ψ f hψ hfΓ hb hj q y _

include hsum

theorem continuous_whittakerSumGL_col (g : AdelicGL F (r + 1)) :
    Continuous (fun y : Fin (r + 1) → Adeles F =>
      whittakerSumGL F ψ f (j + 1) (by omega) (colUnit (colIdx j hj) y * g)) := by
  have h := funext (whittakerSumGL_colUnit_mul F ψ f hψ hfΓ hb hj (g := g))
  rw [h]
  exact continuous_tsum_pairingCharacter _ _ (hsum _)

omit hsum in
theorem isPeriodic_whittakerSumGL_col (g : AdelicGL F (r + 1)) :
    IsPeriodic (fun y : Fin (r + 1) → Adeles F =>
      whittakerSumGL F ψ f (j + 1) (by omega) (colUnit (colIdx j hj) y * g)) := by
  have h := funext (whittakerSumGL_colUnit_mul F ψ f hψ hfΓ hb hj (g := g))
  rw [h]
  exact isPeriodic_tsum_pairingCharacter _ _

variable [CompactSpace (AdeleQuotient F)]

open scoped Classical in
theorem fourierCoeff_whittakerSumGL_col (g : AdelicGL F (r + 1)) (a₀ : Fin (r + 1) → F) :
    fourierCoeff (fun y : Fin (r + 1) → Adeles F =>
      whittakerSumGL F ψ f (j + 1) (by omega) (colUnit (colIdx j hj) y * g)) a₀ =
      ∑' q : UnipotentRationalCosets F (j + 1), if rowChar F b q = a₀ then
        whittaker F r ψ f (padRational F (by omega : j + 1 ≤ r + 1) q.out *
          (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm g) else 0 := by
  have h := funext (whittakerSumGL_colUnit_mul F ψ f hψ hfΓ hb hj (g := g))
  rw [h]
  exact fourierCoeff_tsum_pairingCharacter _ _ (hsum _) a₀

/-- The zeroth Fourier coefficient of `G_(j+1)` along column `j + 1` vanishes. -/
theorem fourierCoeff_zero_whittakerSumGL_col (hb0 : b ≠ 0) (g : AdelicGL F (r + 1)) :
    fourierCoeff (fun y : Fin (r + 1) → Adeles F =>
      whittakerSumGL F ψ f (j + 1) (by omega) (colUnit (colIdx j hj) y * g)) 0 = 0 := by
  classical
  rw [fourierCoeff_whittakerSumGL_col F ψ f hψ hfΓ hb hj hsum g 0]
  refine (tsum_congr fun q => ?_).trans tsum_zero
  exact ite_eq_right (rowChar_ne_zero F hb0 q (by omega))

/-- **Step.** The coefficient of `G̃_(j+1)` along column `j + 1` at `ψ₀(b y_j)` is `G̃_j`. -/
theorem colCoeffB_whittakerSumGL (hb0 : b ≠ 0) (g : AdelicGL F (r + 1)) :
    colCoeffB hj b (whittakerSumGL F ψ f (j + 1) (by omega)) g =
      whittakerSumGL F ψ f j (by omega) g := by
  classical
  unfold colCoeffB
  rw [fourierCoeff_whittakerSumGL_col F ψ f hψ hfΓ hb hj hsum g]
  set x := (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm g with hx
  set φ : UnipotentRationalCosets F (j + 1) → ℂ := fun q =>
    if rowChar F b q = Pi.single (charIdx j hj) b then
      whittaker F r ψ f (padRational F (by omega : j + 1 ≤ r + 1) q.out * x) else 0 with hφ
  have hsupp : Function.support φ ⊆ Set.range (cosetPad F j) := by
    intro q hq
    rw [Function.mem_support] at hq
    by_cases hc : rowChar F b q = Pi.single (charIdx j hj) b
    · exact (lastRowStandard_out_iff F q).mp ((rowChar_eq_single_iff F hj hb0 q).mp hc)
    · exact absurd (ite_eq_right hc) hq
  change ∑' q, φ q = _
  rw [← (cosetPad_injective F).tsum_eq hsupp]
  unfold whittakerSumGL whittakerSum
  refine tsum_congr fun q => ?_
  have hc : rowChar F b (cosetPad F j q) = Pi.single (charIdx j hj) b :=
    (rowChar_eq_single_iff F hj hb0 _).mpr ((lastRowStandard_out_iff F _).mpr ⟨q, rfl⟩)
  simp only [hφ]
  rw [ite_eq_left hc, whittaker_padRational_cosetPad F ψ f hψ hfΓ]

end Column

end Invariance

end Sum

end Langlands.Global.RankinSelbergGlobal.Unfolding
