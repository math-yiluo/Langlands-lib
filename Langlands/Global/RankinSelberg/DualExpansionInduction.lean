import Langlands.Global.RankinSelberg.DualExpansionStep
import Langlands.Automorphic.CuspidalWhittaker.Columns

/-! # Regularity and invariance of the rectangle periods -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global
open Langlands.Automorphic.CuspidalWhittaker (IsPeriodic ratVec ratVec_apply ratMulVec
  ratMulVec_apply preservesRational_ratMulVec continuous_ratMulVec ratMulVec_ratMulVec ratMulVec_one)

variable {F : Type u} [Field F] [NumberField F]

local instance dualIndSchemeAffine (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dualIndSchemeSmooth (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable {m K : ℕ}

section LastEntry

theorem continuous_lastEntry : Continuous (lastEntry : (Fin K → Adeles F) → Adeles F) := by
  unfold lastEntry
  exact continuous_finsetSum _ fun i _ => by
    split_ifs
    · exact continuous_apply i
    · exact continuous_const

theorem lastEntry_add {R : Type*} [AddCommMonoid R] (c d : Fin K → R) :
    lastEntry (c + d) = lastEntry c + lastEntry d := by
  unfold lastEntry
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem isPeriodic_lastEntry {ψ : AddChar (Adeles F) ℂ}
    (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) :
    IsPeriodic (fun c : Fin K → Adeles F => ψ (lastEntry c)) := by
  intro c σ
  simp only
  rw [lastEntry_add, AddChar.map_add_eq_mul]
  have : lastEntry (ratVec σ : Fin K → Adeles F) = algebraMap F (Adeles F) (lastEntry σ) := by
    unfold lastEntry
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [this, hψF, mul_one]

theorem lastEntry_mulVec_unitriangular {R : Type*} [CommRing R] {U : Matrix (Fin K) (Fin K) R}
    (hU : PrimitiveAdelicHeight.IsUnitriangular U) (c : Fin K → R) :
    lastEntry (U.mulVec c) = lastEntry c := by
  cases K with
  | zero => simp [lastEntry]
  | succ k =>
    rw [lastEntry_succ, lastEntry_succ]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single (Fin.last k)]
    · have h1 : U (Fin.last k) (Fin.last k) = 1 := hU.2 _
      simp only [h1, one_mul]
    · intro j _ hj
      have h0 : U (Fin.last k) j = 0 := hU.1 (lt_of_le_of_ne (Fin.le_last j) hj)
      simp only [h0, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

end LastEntry

section Kronecker

theorem ratMulVec_kron (M : Matrix (Fin K) (Fin K) F) (x : Fin K × Fin m → Adeles F) :
    ratMulVec (Matrix.kronecker M (1 : Matrix (Fin m) (Fin m) F)) x =
      rowMulRect F (M.map (algebraMap F (Adeles F))) x := by
  funext p
  simp only [ratMulVec_apply, Matrix.mulVec, dotProduct, rowMulRect, Matrix.map_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply,
    mul_ite, mul_one, mul_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single p.2]
  · simp
  · intro l _ hl
    simp [Ne.symm hl]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem surjective_ratMulVec_kron (M : RationalGL F K) :
    Function.Surjective (ratMulVec (Matrix.kronecker (M : Matrix (Fin K) (Fin K) F)
      (1 : Matrix (Fin m) (Fin m) F))) := fun z =>
  ⟨ratMulVec (Matrix.kronecker ((M⁻¹ : RationalGL F K) : Matrix (Fin K) (Fin K) F)
      (1 : Matrix (Fin m) (Fin m) F)) z, by
    rw [ratMulVec_ratMulVec]
    simp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    convert ratMulVec_one z
    exact Matrix.one_kronecker_one⟩

end Kronecker

section RectRegularity

variable [CompactSpace (AdeleQuotient F)] {ψ : AddChar (Adeles F) ℂ}
  (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) (hψc : Continuous ψ)
  {V : Points F (m + K + 1) → ℂ}

variable (ψ) in
/-- The inner column integral of a rectangle period. -/
def rectInner (G : Points F (m + K + 1) → ℂ) (g : Points F (m + K + 1))
    (x : Fin K × Fin m → Adeles F) : ℂ :=
  Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K) fun c =>
    ψ (lastEntry c) * G (xcPoint F x c * g)

theorem rectPeriod_eq_rectInner (G : Points F (m + K + 1) → ℂ) (g : Points F (m + K + 1)) :
    rectPeriod F m K ψ G g =
      Langlands.Automorphic.CuspidalWhittaker.torusIntegral (Fin K × Fin m) (rectInner ψ G g) :=
  rfl

omit [CompactSpace (AdeleQuotient F)] in
include hψF in
theorem DualData.isPeriodic_rectIntegrand (hV : DualData F m ψ K V) (x : Fin K × Fin m → Adeles F)
    (g : Points F (m + K + 1)) :
    IsPeriodic (fun c : Fin K → Adeles F => ψ (lastEntry c) * cornerSum F m K V (xcPoint F x c * g)) :=
  (isPeriodic_lastEntry hψF).mul (hV.isPeriodic_col hψF x g)

include hψF in
theorem DualData.isPeriodic_rectInner (hV : DualData F m ψ K V) (g : Points F (m + K + 1)) :
    IsPeriodic (rectInner ψ (cornerSum F m K V) g) := by
  intro x ρ
  refine Langlands.Automorphic.CuspidalWhittaker.torusIntegral_congr fun c => ?_
  have h : cornerSum F m K V (xcPoint F (x + ratVec ρ) c * g) =
      cornerSum F m K V (xcPoint F x c * g) := hV.isPeriodic_rect hψF c g x ρ
  rw [h]

include hψF hψc in
theorem DualData.continuous_rectInner_param {X : Type*} [TopologicalSpace X]
    (hV : DualData F m ψ K V) {φ : X → Points F (m + K + 1)} (hφ : Continuous φ) :
    Continuous (fun p : X × (Fin K × Fin m → Adeles F) =>
      rectInner ψ (cornerSum F m K V) (φ p.1) p.2) := by
  unfold rectInner
  refine Langlands.Automorphic.CuspidalWhittaker.continuous_torusIntegral ?_
    (fun p => hV.isPeriodic_rectIntegrand hψF p.2 (φ p.1))
  have hxc := continuous_xcPoint (F := F) (m := m) (K := K)
  have h1 : Continuous fun q : (X × (Fin K × Fin m → Adeles F)) × (Fin K → Adeles F) =>
      xcPoint F q.1.2 q.2 :=
    hxc.comp (f := fun q : (X × (Fin K × Fin m → Adeles F)) × (Fin K → Adeles F) =>
      (q.1.2, q.2)) (by fun_prop)
  exact (hψc.comp (continuous_lastEntry.comp continuous_snd)).mul
    (hV.continuous_cornerSum.comp (h1.mul (hφ.comp (continuous_fst.comp continuous_fst))))

include hψF hψc in
theorem DualData.continuous_rectPeriod_param {X : Type*} [TopologicalSpace X]
    (hV : DualData F m ψ K V) {φ : X → Points F (m + K + 1)} (hφ : Continuous φ) :
    Continuous (fun p : X => rectPeriod F m K ψ (cornerSum F m K V) (φ p)) := by
  simp only [rectPeriod_eq_rectInner]
  have h1 : Continuous (Function.uncurry fun p : X => rectInner ψ (cornerSum F m K V) (φ p)) :=
    hV.continuous_rectInner_param hψF hψc hφ
  exact Langlands.Automorphic.CuspidalWhittaker.continuous_torusIntegral
    (F := fun p : X => rectInner ψ (cornerSum F m K V) (φ p)) h1
    (fun p => hV.isPeriodic_rectInner hψF (φ p))

include hψF hψc in
theorem DualData.continuous_rectInner (hV : DualData F m ψ K V) (g : Points F (m + K + 1)) :
    Continuous (rectInner ψ (cornerSum F m K V) g) := by
  unfold rectInner
  refine Langlands.Automorphic.CuspidalWhittaker.continuous_torusIntegral ?_
    (fun x => hV.isPeriodic_rectIntegrand hψF x g)
  have h1 : Continuous fun q : (Fin K × Fin m → Adeles F) × (Fin K → Adeles F) =>
      xcPoint F q.1 q.2 := continuous_xcPoint
  exact (hψc.comp (continuous_lastEntry.comp continuous_snd)).mul
    (hV.continuous_cornerSum.comp (h1.mul continuous_const))

include hψF hψc in
/-- The rectangle periods are left invariant under the rational points of the middle block. -/
theorem DualData.rectPeriod_midPoint_rat_mul (hV : DualData F m ψ K V) {g : unipotentAdelic F K}
    (hg : g ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F K) (upperUnipotent F K))
    (u : Points F K) (y : Points F (m + K + 1)) :
    rectPeriod F m K ψ (cornerSum F m K V) (midPoint F ((g : Points F K) * u) * y) =
      rectPeriod F m K ψ (cornerSum F m K V) (midPoint F u * y) := by
  obtain ⟨M, hM⟩ := (mem_rationalSubgroup_unipotent_iff g⁻¹).mp (inv_mem hg)
  obtain ⟨U, hU⟩ : ∃ U, U = pointMatrix F ((g⁻¹ : unipotentAdelic F K) : Points F K) :=
    ⟨_, rfl⟩
  have hUM : U = (M : Matrix (Fin K) (Fin K) F).map (algebraMap F (Adeles F)) := by
    rw [hU, hM, pointMatrix_symm_rational]
  have hUu : PrimitiveAdelicHeight.IsUnitriangular U := by
    rw [hU]; exact isUnitriangular_of_mem_unipotentAdelic F g⁻¹
  have hpt : ∀ x c, xcPoint F x c * (midPoint F ((g : Points F K) * u) * y) =
      midPoint F (g : Points F K) * (xcPoint F (rowMulRect F U x) (U.mulVec c) *
        (midPoint F u * y)) := by
    intro x c
    have h := midPoint_inv_conj (m := m) ((g⁻¹ : unipotentAdelic F K) : Points F K) x c
    have hg' : (((g⁻¹ : unipotentAdelic F K) : Points F K))⁻¹ = (g : Points F K) := by
      rw [Subgroup.coe_inv, inv_inv]
    rw [hg', ← hU] at h
    rw [midPoint_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (xcPoint F x c), h, mul_assoc]
  set Z := midPoint F u * y with hZ
  rw [rectPeriod_eq_rectInner, rectPeriod_eq_rectInner]
  have hinner : ∀ x, rectInner ψ (cornerSum F m K V) (midPoint F ((g : Points F K) * u) * y) x =
      rectInner ψ (cornerSum F m K V) Z (rowMulRect F U x) := by
    intro x
    unfold rectInner
    simp_rw [hpt x, hV.cornerSum_midPoint_rat_mul hψF hg]
    rw [← Langlands.Automorphic.CuspidalWhittaker.torusIntegral_comp
      (hV.isPeriodic_rectIntegrand hψF (rowMulRect F U x) Z)
      ((hψc.comp continuous_lastEntry).mul (hV.continuous_cornerSum.comp
        ((continuous_xcPoint_right _).mul continuous_const)))
      (preservesRational_ratMulVec (M : Matrix (Fin K) (Fin K) F))
      (continuous_ratMulVec _) (Langlands.Automorphic.CuspidalWhittaker.surjective_ratMulVec M)]
    refine Langlands.Automorphic.CuspidalWhittaker.torusIntegral_congr fun c => ?_
    simp only [ratMulVec_apply, ← hUM]
    rw [lastEntry_mulVec_unitriangular hUu]
  rw [Langlands.Automorphic.CuspidalWhittaker.torusIntegral_congr hinner]
  have hrw : (fun x => rectInner ψ (cornerSum F m K V) Z (rowMulRect F U x)) =
      fun x => rectInner ψ (cornerSum F m K V) Z
        (ratMulVec (Matrix.kronecker (M : Matrix (Fin K) (Fin K) F)
          (1 : Matrix (Fin m) (Fin m) F)) x) := by
    funext x
    rw [ratMulVec_kron, ← hUM]
  rw [hrw, Langlands.Automorphic.CuspidalWhittaker.torusIntegral_comp
    (hV.isPeriodic_rectInner hψF Z)
    (hV.continuous_rectInner hψF hψc Z)
    (preservesRational_ratMulVec _) (continuous_ratMulVec _) (surjective_ratMulVec_kron M)]

end RectRegularity

end Langlands.Global.RankinSelbergGlobal.Unfolding
