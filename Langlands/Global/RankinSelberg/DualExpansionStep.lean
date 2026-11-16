import Langlands.Global.RankinSelberg.DualExpansionRectangle

/-! # The induction step for the dual expansion -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global
open Langlands.Automorphic.CuspidalWhittaker (IsPeriodic ratVec ratVec_apply)

variable {F : Type u} [Field F] [NumberField F]

local instance dualStepSchemeAffine (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dualStepSchemeSmooth (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

instance numberFieldCountable : Countable F :=
  (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable

variable {m K : ℕ}

section Orthogonality

theorem lastEntry_succ {R : Type*} [AddCommMonoid R] (c : Fin (K + 1) → R) :
    lastEntry c = c (Fin.last K) := by
  unfold lastEntry
  rw [Finset.sum_eq_single (Fin.last K)]
  · simp
  · intro i _ hi
    rw [ite_eq_right (fun h => hi (Fin.ext (by simp; omega)))]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The coefficients of the column character attached to a coset representative. -/
def survivorCoeff (q : UnipotentRationalCosets F (m + (K + 1))) : Fin (K + 1) → F := fun i =>
  (if (i : ℕ) = K then 1 else 0) -
    (q.out : Matrix (Fin (m + (K + 1))) (Fin (m + (K + 1))) F) (Fin.last (m + K)) ⟨m + i, by omega⟩

omit [NumberField F] in
theorem survivorCoeff_eq_zero_iff (q : UnipotentRationalCosets F (m + (K + 1))) :
    survivorCoeff q = 0 ↔ SurvivorRow F (m := m) (K := K) q.out := by
  constructor
  · intro h i
    have := congrFun h i
    simp only [survivorCoeff, Pi.zero_apply, sub_eq_zero] at this
    exact this.symm
  · intro h
    funext i
    simp only [survivorCoeff, Pi.zero_apply, sub_eq_zero]
    exact (h i).symm

theorem lastEntry_mulVec_extC (q : RationalGL F (m + (K + 1))) (c : Fin (K + 1) → Adeles F) :
    lastEntry (Matrix.mulVec ((AdelicGL.rational F (m + (K + 1)) q : AdelicGL F (m + (K + 1))) :
      Matrix (Fin (m + (K + 1))) (Fin (m + (K + 1))) (Adeles F)) (extC (m := m) c)) =
      ∑ i : Fin (K + 1), algebraMap F (Adeles F)
        ((q : Matrix (Fin (m + (K + 1))) (Fin (m + (K + 1))) F) (Fin.last (m + K))
          ⟨m + i, by omega⟩) * c i := by
  rw [lastEntry_succ]
  simp only [Matrix.mulVec, dotProduct, AdelicGL.rational_apply, extC]
  rw [Fin.sum_univ_add]
  rw [Finset.sum_eq_zero (fun a _ => by
      simp), zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : m ≤ ((Fin.natAdd m i : Fin (m + (K + 1))) : ℕ) := by simp
  simp only [this, dite_true]
  congr 2
  ext; simp

variable {ψ : AddChar (Adeles F) ℂ} {W : Points F (m + (K + 1) + 1) → ℂ}

/-- The column character of a corner term. -/
theorem DualData.cornerFamily_xcPoint (hW : DualData F m ψ (K + 1) W)
    (q : UnipotentRationalCosets F (m + (K + 1))) (x : Fin (K + 1) × Fin m → Adeles F)
    (c : Fin (K + 1) → Adeles F) (z : Points F (m + (K + 1) + 1)) :
    ψ (lastEntry c) * cornerFamily F m (K + 1) W q (xcPoint F x c * z) =
      pairChar ψ (survivorCoeff q) c * cornerFamily F m (K + 1) W q (xcPoint F x 0 * z) := by
  have hsplit : xcPoint F x c = xcPoint F 0 c * xcPoint F x 0 := by
    rw [xcPoint_mul, zero_add, add_zero]
  unfold cornerFamily
  rw [hsplit, xcPoint_zero_eq_lastColPoint, mul_assoc, ← mul_assoc (padRational F _ q.out)]
  rw [padRational_mul_lastColPoint, mul_assoc, hW.lastColPoint_mul, ← mul_assoc]
  congr 1
  rw [← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul]
  unfold pairChar
  congr 1
  rw [lastEntry_mulVec_extC, lastEntry_succ]
  simp only [survivorCoeff, map_sub, sub_mul, Finset.sum_sub_distrib, apply_ite (algebraMap F _),
    map_one, map_zero, ite_mul, one_mul, zero_mul]
  have hK : (∑ x : Fin (K + 1), if (x : ℕ) = K then c x else 0) = c (Fin.last K) := by
    rw [Finset.sum_eq_single (Fin.last K)]
    · simp
    · intro i _ hi
      rw [ite_eq_right (fun h => hi (Fin.ext (by simp; omega)))]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hK, sub_eq_add_neg]

theorem norm_pairChar_eq_one {T : Type*} [Fintype T] (hψ1 : ∀ x, ‖ψ x‖ = 1) (a : T → F)
    (y : T → Adeles F) : ‖pairChar ψ a y‖ = 1 :=
  hψ1 _

open Classical in
/-- **Column orthogonality**: integrating the last column against `ψ` keeps exactly the
surviving cosets. -/
theorem DualData.torusIntegral_cornerSum_col [CompactSpace (AdeleQuotient F)]
    (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) (hψc : Continuous ψ)
    (hψ1 : ∀ x, ‖ψ x‖ = 1)
    (hψn : ∀ a : F, a ≠ 0 → ∃ y : Adeles F, ψ (algebraMap F (Adeles F) a * y) ≠ 1)
    (hW : DualData F m ψ (K + 1) W) (x : Fin (K + 1) × Fin m → Adeles F)
    (z : Points F (m + (K + 1) + 1)) :
    Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin (K + 1)) (fun c =>
        ψ (lastEntry c) * cornerSum F m (K + 1) W (xcPoint F x c * z)) =
      ∑' q, if SurvivorRow F (m := m) (K := K) q.out then
        cornerFamily F m (K + 1) W q (xcPoint F x 0 * z) else 0 := by
  classical
  have hrw : (fun c : Fin (K + 1) → Adeles F =>
      ψ (lastEntry c) * cornerSum F m (K + 1) W (xcPoint F x c * z)) =
      fun c => ∑' q, pairChar ψ (survivorCoeff q) c *
        cornerFamily F m (K + 1) W q (xcPoint F x 0 * z) := by
    funext c
    unfold cornerSum
    rw [← tsum_mul_left]
    exact tsum_congr fun q => hW.cornerFamily_xcPoint q x c z
  rw [hrw, torusIntegral_tsum
    (B := ∑' q, ‖cornerFamily F m (K + 1) W q (xcPoint F x 0 * z)‖)]
  · refine tsum_congr fun q => ?_
    rw [Langlands.Automorphic.CuspidalWhittaker.torusIntegral_mul_const,
      torusIntegral_pairChar ψ hψF hψn]
    by_cases hq : SurvivorRow F (m := m) (K := K) q.out
    · rw [ite_eq_left ((survivorCoeff_eq_zero_iff q).mpr hq), ite_eq_left hq, one_mul]
    · rw [ite_eq_right (fun h => hq ((survivorCoeff_eq_zero_iff q).mp h)), ite_eq_right hq,
        zero_mul]
  · exact fun q => (continuous_pairChar ψ hψc _).mul continuous_const
  · exact fun q => (isPeriodic_pairChar ψ hψF _).mul
      (Langlands.Automorphic.CuspidalWhittaker.isPeriodic_const _)
  · intro c
    simp only [norm_mul, norm_pairChar_eq_one hψ1, one_mul]
    exact hW.summable.1 _
  · intro c
    simp only [norm_mul, norm_pairChar_eq_one hψ1, one_mul, le_refl]

end Orthogonality

section Survivors

variable {ψ : AddChar (Adeles F) ℂ} {W : Points F (m + (K + 1) + 1) → ℂ}

open Classical in
/-- **Survivor reindexing**. -/
theorem tsum_survivorRow_eq (f : UnipotentRationalCosets F (m + (K + 1)) → ℂ) :
    (∑' q, if SurvivorRow F (m := m) (K := K) q.out then f q else 0) =
      ∑' p : UnipotentRationalCosets F (m + K) × (Fin m → F), f (survivorMap F p) := by
  have h := (survivorMap_injective (F := F) (m := m) (K := K)).tsum_eq
    (f := fun q : UnipotentRationalCosets F (m + K + 1) =>
      if SurvivorRow F (m := m) (K := K) q.out then f q else 0) (by
      intro q hq
      by_contra hq'
      apply hq
      simp only
      rw [ite_eq_right]
      intro hs
      exact hq' (exists_survivorMap_eq F q hs))
  refine h.symm.trans (tsum_congr fun p => ?_)
  exact ite_eq_left (survivorRow_out_survivorMap F p)

theorem rational_rowRat (β : Fin m → F) :
    AdelicGL.rational F (m + K + 1) (rowRat F (K := K) β) =
      Langlands.Automorphic.CuspidalWhittaker.sqZeroUnit
        (rowMat m K fun j => algebraMap F (Adeles F) (β j)) (rowMat_mul_rowMat _ _) := by
  apply Units.ext
  ext a b
  simp only [rowRat, AdelicGL.rational_apply, Langlands.Automorphic.CuspidalWhittaker.sqZeroUnit_val,
    Matrix.add_apply, rowMat, Matrix.one_apply]
  split_ifs <;> simp

theorem padRational_rowRat (β : Fin m → F) :
    padRational F (Nat.le_succ (m + K + 1)) (rowRat F (K := K) β) =
      pad F (Nat.le_succ (m + K + 1)) (rowPoint F (K := K) fun j => algebraMap F (Adeles F) (β j)) := by
  unfold padRational pad rowPoint
  rw [rational_rowRat, MulEquiv.apply_symm_apply]

/-- A surviving corner term at rank `m + K + 2` is a corner term of the pullback at rank
`m + K + 1`. -/
theorem DualData.cornerFamily_survivorMap (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1)
    (hW : DualData F m ψ (K + 1) W) (y : Points F (m + (K + 1) + 1))
    (p : UnipotentRationalCosets F (m + K) × (Fin m → F)) (x : Fin (K + 1) × Fin m → Adeles F)
    (h : Points F (m + K + 1)) :
    cornerFamily F m (K + 1) W (survivorMap F p)
        (xcPoint F x 0 * (pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega) h * y)) =
      cornerFamily F m K (dualPullback W y) p.1
        (xcPoint F (restOfRect F x) 0 *
          rowPoint F (rowOfRect F x + fun j => algebraMap F (Adeles F) (p.2 j)) * h) := by
  obtain ⟨q', β⟩ := p
  have h1 : QuotientGroup.rightRel (rationalUpperUnipotent F (m + K + 1))
      (padGL (Nat.le_succ (m + K)) q'.out * rowRat F β) (survivorMap F (q', β)).out :=
    Quotient.exact (Quotient.out_eq _).symm
  have hrow : rowPoint F (K := K) (fun j => algebraMap F (Adeles F) (β j)) *
      (xcPoint F (restOfRect F x) 0 * rowPoint F (rowOfRect F x)) =
      xcPoint F (restOfRect F x) 0 *
        rowPoint F (rowOfRect F x + fun j => algebraMap F (Adeles F) (β j)) := by
    rw [← mul_assoc, rowPoint_mul_xcPoint]
    have : outerRect (0 : Fin K → Adeles F) (fun j => algebraMap F (Adeles F) (β j)) = 0 := by
      funext q; simp [outerRect]
    rw [this, sub_zero, mul_assoc, rowPoint_mul]
    congr 2
    exact add_comm _ _
  have hpt : padRational F (Nat.le_succ (m + K + 1)) (padGL (Nat.le_succ (m + K)) q'.out *
        rowRat F β) * (xcPoint F x 0 * (pad F (Nat.le_succ (m + K + 1)) h * y)) =
      pad F (Nat.le_succ (m + K + 1)) (padRational F (Nat.le_succ (m + K)) q'.out *
        (xcPoint F (restOfRect F x) 0 *
          rowPoint F (rowOfRect F x + fun j => algebraMap F (Adeles F) (β j)) * h)) * y := by
    rw [padRational_mul, padRational_padGL, padRational_rowRat, xcPoint_succ_rect,
      ← pad_padRational (Nat.le_succ (m + K)) (Nat.le_succ (m + K + 1)), ← hrow]
    simp only [pad_mul, mul_assoc]
  unfold cornerFamily dualPullback
  rw [hW.padRational_of_rightRel hψF _ h1]
  exact congrArg W hpt

end Survivors

section ColumnStep

variable {ψ : AddChar (Adeles F) ℂ} {W : Points F (m + (K + 1) + 1) → ℂ}

/-- **Column step**: integrating the last column of the rectangle turns the corner sum at rank
`m + K + 2` into the sum over rational rows of corner sums of the pullback. -/
theorem DualData.torusIntegral_col_eq_pullback [CompactSpace (AdeleQuotient F)]
    (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) (hψc : Continuous ψ)
    (hψ1 : ∀ x, ‖ψ x‖ = 1)
    (hψn : ∀ a : F, a ≠ 0 → ∃ y : Adeles F, ψ (algebraMap F (Adeles F) a * y) ≠ 1)
    (hW : DualData F m ψ (K + 1) W) (y : Points F (m + (K + 1) + 1))
    (x : Fin (K + 1) × Fin m → Adeles F) (h : Points F (m + K + 1)) :
    Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin (K + 1)) (fun c =>
        ψ (lastEntry c) * cornerSum F m (K + 1) W
          (xcPoint F x c * (pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega) h * y))) =
      ∑' β : Fin m → F, cornerSum F m K (dualPullback W y)
        (xcPoint F (restOfRect F x) 0 *
          rowPoint F (rowOfRect F x + fun j => algebraMap F (Adeles F) (β j)) * h) := by
  rw [hW.torusIntegral_cornerSum_col hψF hψc hψ1 hψn, tsum_survivorRow_eq]
  set Z := xcPoint F x 0 * (pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega) h * y)
  set G : UnipotentRationalCosets F (m + K) × (Fin m → F) → ℂ :=
    fun p => cornerFamily F m (K + 1) W (survivorMap F p) Z
  have hGs : Summable G :=
    (((hW.summable.1 Z).comp_injective (survivorMap_injective (F := F) (m := m) (K := K)))).of_norm
  have hswap : Summable (G ∘ (Equiv.prodComm _ _)) :=
    (Equiv.prodComm _ _).summable_iff.mpr hGs
  rw [← (Equiv.prodComm _ _).tsum_eq G]
  refine (hswap.tsum_prod' (fun b => hswap.prod_factor b)).trans (tsum_congr fun β => ?_)
  unfold cornerSum
  refine tsum_congr fun q' => ?_
  exact hW.cornerFamily_survivorMap hψF y (q', β) x h

end ColumnStep

section Split

/-- Splitting the rows of a `(K+1) × m` rectangle into the last row and the others. -/
def rectSplit : Fin m ⊕ (Fin K × Fin m) ≃ Fin (K + 1) × Fin m where
  toFun := Sum.elim (fun j => (Fin.last K, j)) (fun p => (p.1.castSucc, p.2))
  invFun p := Fin.lastCases (motive := fun _ => Fin m ⊕ (Fin K × Fin m)) (Sum.inl p.2)
    (fun i => Sum.inr (i, p.2)) p.1
  left_inv s := by
    rcases s with j | ⟨i, j⟩
    · simp
    · simp
  right_inv p := by
    obtain ⟨i, j⟩ := p
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · simp
    · simp

/-- The rectangle with rows `x'` and last row `b`. -/
def joinRect {R : Type*} (x' : Fin K × Fin m → R) (b : Fin m → R) : Fin (K + 1) × Fin m → R :=
  fun k => Sum.elim b x' (rectSplit.symm k)

theorem restOfRect_joinRect (x' : Fin K × Fin m → Adeles F) (b : Fin m → Adeles F) :
    restOfRect F (joinRect x' b) = x' := by
  funext p
  simp [restOfRect, joinRect, rectSplit]

theorem rowOfRect_joinRect (x' : Fin K × Fin m → Adeles F) (b : Fin m → Adeles F) :
    rowOfRect F (joinRect x' b) = b := by
  funext j
  simp [rowOfRect, joinRect, rectSplit]

variable [CompactSpace (AdeleQuotient F)]

/-- **Row split of rectangle torus integrals**. -/
theorem torusIntegral_rect_succ {f : (Fin (K + 1) × Fin m → Adeles F) → ℂ} (hf : IsPeriodic f)
    (hc : Continuous f) :
    Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin (K + 1) × Fin m) f =
      Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin m) fun b =>
        Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K × Fin m) fun x' =>
          f (joinRect x' b) := by
  rw [← torusIntegral_reindex (rectSplit (m := m) (K := K)) hf hc]
  refine torusIntegral_sum_elim ?_ ?_
  · intro y k
    have := hf (fun k => y (rectSplit.symm k)) (fun p => k (rectSplit.symm p))
    convert this using 2
    funext p
    simp [ratVec]
  · exact hc.comp (continuous_pi fun k => continuous_apply _)

end Split

section Shift

theorem xcPoint_rowPoint_shift (x' : Fin K × Fin m → Adeles F) (c' : Fin K → Adeles F)
    (b' : Fin m → Adeles F) (u : Points F K) :
    xcPoint F x' 0 * rowPoint F b' * (xcPoint F 0 c' * midPoint F u) =
      xcPoint F (x' - outerRect c' b') c' * midPoint F u * rowPoint F b' := by
  rw [mul_assoc, ← mul_assoc (rowPoint F b'), rowPoint_mul_xcPoint, mul_assoc, rowPoint_mul_midPoint,
    ← mul_assoc, ← mul_assoc, xcPoint_mul, zero_sub, ← sub_eq_add_neg, zero_add]

variable {ψ : AddChar (Adeles F) ℂ} (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1)
  {V : Points F (m + K + 1) → ℂ}
include hψF

theorem DualData.isPeriodic_rect (hV : DualData F m ψ K V) (c' : Fin K → Adeles F)
    (g : Points F (m + K + 1)) :
    IsPeriodic (fun x' => cornerSum F m K V (xcPoint F x' c' * g)) := by
  intro x' ρ
  have : xcPoint F (x' + ratVec ρ) c' =
      xcPoint F (fun p => algebraMap F (Adeles F) (ρ p)) (fun i => algebraMap F (Adeles F)
        ((0 : Fin K → F) i)) * xcPoint F x' c' := by
    rw [xcPoint_mul]
    congr 1
    · rw [add_comm]; rfl
    · funext i; simp
  simp only
  rw [this, mul_assoc, hV.cornerSum_xcPoint_rat_mul hψF]

theorem DualData.isPeriodic_col (hV : DualData F m ψ K V) (x' : Fin K × Fin m → Adeles F)
    (g : Points F (m + K + 1)) :
    IsPeriodic (fun c' => cornerSum F m K V (xcPoint F x' c' * g)) := by
  intro c' σ
  have : xcPoint F x' (c' + ratVec σ) =
      xcPoint F (fun p => algebraMap F (Adeles F) ((0 : Fin K × Fin m → F) p))
        (fun i => algebraMap F (Adeles F) (σ i)) * xcPoint F x' c' := by
    rw [xcPoint_mul]
    congr 1
    · funext p; simp
    · rw [add_comm]; rfl
  simp only
  rw [this, mul_assoc, hV.cornerSum_xcPoint_rat_mul hψF]

end Shift

section ColumnBound

variable {ψ : AddChar (Adeles F) ℂ} (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1)
  {W : Points F (m + (K + 1) + 1) → ℂ}
include hψF

/-- The rational row sums of corner sums of the pullback are dominated by the corner sum of
norms at rank `m + K + 2`. -/
theorem DualData.summable_norm_col (hW : DualData F m ψ (K + 1) W) (y : Points F (m + (K + 1) + 1))
    (X : Fin (K + 1) × Fin m → Adeles F) (h : Points F (m + K + 1)) :
    Summable (fun β : Fin m → F => ‖cornerSum F m K (dualPullback W y)
        (xcPoint F (restOfRect F X) 0 *
          rowPoint F (rowOfRect F X + fun j => algebraMap F (Adeles F) (β j)) * h)‖) ∧
      ∑' β : Fin m → F, ‖cornerSum F m K (dualPullback W y)
        (xcPoint F (restOfRect F X) 0 *
          rowPoint F (rowOfRect F X + fun j => algebraMap F (Adeles F) (β j)) * h)‖ ≤
        cornerNormSum F m (K + 1) W
          (xcPoint F X 0 * (pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega) h * y)) := by
  set Z := xcPoint F X 0 * (pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega) h * y)
  set G : (Fin m → F) × UnipotentRationalCosets F (m + K) → ℝ :=
    fun p => ‖cornerFamily F m (K + 1) W (survivorMap F (p.2, p.1)) Z‖
  have hinj : Function.Injective fun p : (Fin m → F) × UnipotentRationalCosets F (m + K) =>
      survivorMap F (p.2, p.1) := by
    intro a b hab
    have := survivorMap_injective (F := F) (m := m) (K := K) hab
    exact Prod.ext (congrArg Prod.snd this) (congrArg Prod.fst this)
  have hGs : Summable G := (hW.summable.1 Z).comp_injective hinj
  have hfib : ∀ β, Summable fun q' => G (β, q') := fun β => hGs.prod_factor β
  have hterm : ∀ β : Fin m → F, ‖cornerSum F m K (dualPullback W y)
      (xcPoint F (restOfRect F X) 0 *
        rowPoint F (rowOfRect F X + fun j => algebraMap F (Adeles F) (β j)) * h)‖ ≤
      ∑' q', G (β, q') := by
    intro β
    unfold cornerSum
    have : (fun q' => cornerFamily F m K (dualPullback W y) q'
        (xcPoint F (restOfRect F X) 0 *
          rowPoint F (rowOfRect F X + fun j => algebraMap F (Adeles F) (β j)) * h)) =
        fun q' => cornerFamily F m (K + 1) W (survivorMap F (q', β)) Z := by
      funext q'
      exact (hW.cornerFamily_survivorMap hψF y (q', β) X h).symm
    rw [this]
    exact norm_tsum_le_tsum_norm (hfib β)
  have hsumfib : Summable fun β => ∑' q', G (β, q') := hGs.prod
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumfib, ?_⟩
  calc _ ≤ ∑' β, ∑' q', G (β, q') :=
        Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
          hsumfib) hsumfib
    _ = ∑' p, G p := (hGs.tsum_prod' hfib).symm
    _ ≤ cornerNormSum F m (K + 1) W Z :=
        tsum_comp_le_tsum_of_inj (hW.summable.1 Z) (fun _ => norm_nonneg _) hinj

end ColumnBound

section ColumnSum

theorem midPoint_colHom_padHom (c' : Fin K → Adeles F) (u : unipotentAdelic F K) :
    midPoint F (m := m) (K := K + 1)
        (((colHom F K (Multiplicative.ofAdd c') * padHom F K u : unipotentAdelic F (K + 1)) :
          Points F (K + 1))) =
      pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega)
        (xcPoint F 0 c' * midPoint F (u : Points F K)) := by
  rw [Subgroup.coe_mul, midPoint_mul, coe_colHom, coe_padHom, midPoint_lastColPoint, midPoint_pad,
    pad_mul]
  rfl

variable {ψ : AddChar (Adeles F) ℂ} {W : Points F (m + (K + 1) + 1) → ℂ}

/-- **The row integrals of the column step** (fixed `u`, `c'`, `b`). -/
theorem DualData.torusIntegral_rect_col [CompactSpace (AdeleQuotient F)]
    (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) (hψc : Continuous ψ)
    (hψ1 : ∀ x, ‖ψ x‖ = 1)
    (hψn : ∀ a : F, a ≠ 0 → ∃ y : Adeles F, ψ (algebraMap F (Adeles F) a * y) ≠ 1)
    (hW : DualData F m ψ (K + 1) W) (y : Points F (m + (K + 1) + 1)) (c' : Fin K → Adeles F)
    (u : unipotentAdelic F K) (b : Fin m → Adeles F) :
    Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K × Fin m) (fun x' =>
      Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin (K + 1)) (fun c =>
        ψ (lastEntry c) * cornerSum F m (K + 1) W (xcPoint F (joinRect x' b) c *
          (pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega)
            (xcPoint F 0 c' * midPoint F (u : Points F K)) * y)))) =
      ∑' β : Fin m → F, Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K × Fin m)
        (fun x' => cornerSum F m K (dualPullback W y)
          (xcPoint F x' c' * midPoint F (u : Points F K) *
            rowPoint F (b + fun j => algebraMap F (Adeles F) (β j)))) := by
  set h := xcPoint F 0 c' * midPoint F (u : Points F K)
  have hV := hW.pullbackData hψF y
  obtain ⟨C, hC⟩ := hW.exists_bound hψF y
  have hpt : ∀ x', Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin (K + 1)) (fun c =>
      ψ (lastEntry c) * cornerSum F m (K + 1) W (xcPoint F (joinRect x' b) c *
        (pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega) h * y))) =
      ∑' β : Fin m → F, cornerSum F m K (dualPullback W y)
        (xcPoint F x' 0 * rowPoint F (b + fun j => algebraMap F (Adeles F) (β j)) * h) := by
    intro x'
    rw [hW.torusIntegral_col_eq_pullback hψF hψc hψ1 hψn y _ h, restOfRect_joinRect,
      rowOfRect_joinRect]
  simp_rw [hpt]
  have hcont : ∀ β : Fin m → F, Continuous fun x' : Fin K × Fin m → Adeles F =>
      cornerSum F m K (dualPullback W y)
        (xcPoint F x' 0 * rowPoint F (b + fun j => algebraMap F (Adeles F) (β j)) * h) := by
    intro β
    have h1 : Continuous fun x' : Fin K × Fin m → Adeles F => xcPoint F (m := m) x' 0 :=
      continuous_xcPoint_left 0
    exact hV.continuous_cornerSum.comp ((h1.mul continuous_const).mul continuous_const)
  have hper : ∀ β : Fin m → F, IsPeriodic fun x' : Fin K × Fin m → Adeles F =>
      cornerSum F m K (dualPullback W y)
        (xcPoint F x' 0 * rowPoint F (b + fun j => algebraMap F (Adeles F) (β j)) * h) := by
    intro β
    have := hV.isPeriodic_rect hψF 0
      (rowPoint F (b + fun j => algebraMap F (Adeles F) (β j)) * h)
    simpa only [mul_assoc] using this
  have hsum : ∀ x' : Fin K × Fin m → Adeles F, Summable fun β : Fin m → F =>
      ‖cornerSum F m K (dualPullback W y)
        (xcPoint F x' 0 * rowPoint F (b + fun j => algebraMap F (Adeles F) (β j)) * h)‖ := by
    intro x'
    have := (hW.summable_norm_col hψF y (joinRect x' b) h).1
    rwa [restOfRect_joinRect, rowOfRect_joinRect] at this
  have hbd : ∀ x' : Fin K × Fin m → Adeles F, ∑' β : Fin m → F,
      ‖cornerSum F m K (dualPullback W y)
        (xcPoint F x' 0 * rowPoint F (b + fun j => algebraMap F (Adeles F) (β j)) * h)‖ ≤ C := by
    intro x'
    have h1 := (hW.summable_norm_col hψF y (joinRect x' b) h).2
    rw [restOfRect_joinRect, rowOfRect_joinRect] at h1
    refine h1.trans ?_
    have h2 := hC (joinRect x' b) 0 (colHom F K (Multiplicative.ofAdd c') * padHom F K u)
    rw [midPoint_colHom_padHom, mul_assoc] at h2
    exact h2
  rw [torusIntegral_tsum hcont hper hsum hbd]
  refine tsum_congr fun β => ?_
  set b' := b + fun j => algebraMap F (Adeles F) (β j)
  have hshift := Langlands.Automorphic.CuspidalWhittaker.torusIntegral_add_right
    (hV.isPeriodic_rect hψF c' (midPoint F (u : Points F K) * rowPoint F b')) (-outerRect c' b')
  have hfun : (fun x' : Fin K × Fin m → Adeles F => cornerSum F m K (dualPullback W y)
      (xcPoint F x' 0 * rowPoint F b' * h)) = fun x' => cornerSum F m K (dualPullback W y)
        (xcPoint F (x' + -outerRect c' b') c' * (midPoint F (u : Points F K) * rowPoint F b')) := by
    funext x'
    rw [xcPoint_rowPoint_shift x' c' b' (u : Points F K), sub_eq_add_neg, mul_assoc]
  rw [hfun, hshift]
  simp only [mul_assoc]

/-- **Uniform bound for the row sums**. -/
theorem DualData.rowJ_bound [CompactSpace (AdeleQuotient F)]
    (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1)
    (hW : DualData F m ψ (K + 1) W) (y : Points F (m + (K + 1) + 1)) :
    ∃ C : ℝ, ∀ (c' : Fin K → Adeles F) (u : unipotentAdelic F K) (b : Fin m → Adeles F),
      Summable (fun β : Fin m → F =>
        ‖Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K × Fin m)
          (fun x' => cornerSum F m K (dualPullback W y)
            (xcPoint F x' c' * midPoint F (u : Points F K) *
              rowPoint F (b + fun j => algebraMap F (Adeles F) (β j))))‖) ∧
      ∑' β : Fin m → F,
        ‖Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K × Fin m)
          (fun x' => cornerSum F m K (dualPullback W y)
            (xcPoint F x' c' * midPoint F (u : Points F K) *
              rowPoint F (b + fun j => algebraMap F (Adeles F) (β j))))‖ ≤ C := by
  have hV := hW.pullbackData hψF y
  obtain ⟨C, hC⟩ := hW.exists_bound hψF y
  refine ⟨C, fun c' u b => ?_⟩
  set h := xcPoint F 0 c' * midPoint F (u : Points F K)
  have hcont : ∀ β : Fin m → F, Continuous fun x' : Fin K × Fin m → Adeles F =>
      cornerSum F m K (dualPullback W y)
        (xcPoint F x' 0 * rowPoint F (b + fun j => algebraMap F (Adeles F) (β j)) * h) := by
    intro β
    have h1 : Continuous fun x' : Fin K × Fin m → Adeles F => xcPoint F (m := m) x' 0 :=
      continuous_xcPoint_left 0
    exact hV.continuous_cornerSum.comp ((h1.mul continuous_const).mul continuous_const)
  have hper : ∀ β : Fin m → F, IsPeriodic fun x' : Fin K × Fin m → Adeles F =>
      cornerSum F m K (dualPullback W y)
        (xcPoint F x' 0 * rowPoint F (b + fun j => algebraMap F (Adeles F) (β j)) * h) := by
    intro β
    have := hV.isPeriodic_rect hψF 0
      (rowPoint F (b + fun j => algebraMap F (Adeles F) (β j)) * h)
    simpa only [mul_assoc] using this
  have hsum : ∀ x' : Fin K × Fin m → Adeles F, Summable fun β : Fin m → F =>
      ‖cornerSum F m K (dualPullback W y)
        (xcPoint F x' 0 * rowPoint F (b + fun j => algebraMap F (Adeles F) (β j)) * h)‖ := by
    intro x'
    have := (hW.summable_norm_col hψF y (joinRect x' b) h).1
    rwa [restOfRect_joinRect, rowOfRect_joinRect] at this
  have hbd : ∀ x' : Fin K × Fin m → Adeles F, ∑' β : Fin m → F,
      ‖cornerSum F m K (dualPullback W y)
        (xcPoint F x' 0 * rowPoint F (b + fun j => algebraMap F (Adeles F) (β j)) * h)‖ ≤ C := by
    intro x'
    have h1 := (hW.summable_norm_col hψF y (joinRect x' b) h).2
    rw [restOfRect_joinRect, rowOfRect_joinRect] at h1
    refine h1.trans ?_
    have h2 := hC (joinRect x' b) 0 (colHom F K (Multiplicative.ofAdd c') * padHom F K u)
    rw [midPoint_colHom_padHom, mul_assoc] at h2
    exact h2
  have hshift : ∀ β : Fin m → F,
      Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K × Fin m)
        (fun x' => cornerSum F m K (dualPullback W y)
          (xcPoint F x' c' * midPoint F (u : Points F K) *
            rowPoint F (b + fun j => algebraMap F (Adeles F) (β j)))) =
      Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K × Fin m)
        (fun x' => cornerSum F m K (dualPullback W y)
          (xcPoint F x' 0 * rowPoint F (b + fun j => algebraMap F (Adeles F) (β j)) * h)) := by
    intro β
    set b' := b + fun j => algebraMap F (Adeles F) (β j)
    have hs := Langlands.Automorphic.CuspidalWhittaker.torusIntegral_add_right
      (hV.isPeriodic_rect hψF c' (midPoint F (u : Points F K) * rowPoint F b')) (-outerRect c' b')
    have hfun : (fun x' : Fin K × Fin m → Adeles F => cornerSum F m K (dualPullback W y)
        (xcPoint F x' 0 * rowPoint F b' * h)) = fun x' => cornerSum F m K (dualPullback W y)
          (xcPoint F (x' + -outerRect c' b') c' * (midPoint F (u : Points F K) * rowPoint F b')) := by
      funext x'
      rw [xcPoint_rowPoint_shift x' c' b' (u : Points F K), sub_eq_add_neg, mul_assoc]
    rw [hfun, hs]
    simp only [mul_assoc]
  have hfin : ∀ s : Finset (Fin m → F), ∑ β ∈ s,
      ‖Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K × Fin m)
        (fun x' => cornerSum F m K (dualPullback W y)
          (xcPoint F x' c' * midPoint F (u : Points F K) *
            rowPoint F (b + fun j => algebraMap F (Adeles F) (β j))))‖ ≤ C := by
    intro s
    simp_rw [hshift]
    exact sum_norm_torusIntegral_le hcont hper hsum hbd s
  have hsm := summable_of_sum_le (fun _ => norm_nonneg _) hfin
  exact ⟨hsm, hsm.tsum_le_of_sum_le hfin⟩

end ColumnSum

end Langlands.Global.RankinSelbergGlobal.Unfolding
