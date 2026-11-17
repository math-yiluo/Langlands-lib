import Langlands.Global.RankinSelberg.WhittakerSimpleRootMoments
import Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerSupport

/-! # Finite-place support in adelic simple-root coordinates -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Classical
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.Automorphic.CuspidalWhittaker
open Langlands.GroupScheme.GeneralLinear

local instance simpleRootFiniteSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

section Algebra

variable {A : Type*} [CommRing A] {r : ℕ}

/-- Conjugation cancels the diagonal ratio in a simple-root unipotent. -/
theorem diagonal_conj_one_add_simpleRootColumn (i : Fin r)
    (d : Fin (r + 1) → Aˣ) (z : A) :
    (((diagonalMatrixUnits A d)⁻¹ : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) A) *
        (1 + colMatrix (i : ℕ) (Pi.single i.castSucc
          ((d i.castSucc : A) * ((d i.succ)⁻¹ : Aˣ) * z))) *
        (diagonalMatrixUnits A d : Matrix (Fin (r + 1)) (Fin (r + 1)) A) =
      1 + colMatrix (i : ℕ) (Pi.single i.castSucc z) := by
  rw [mul_add, add_mul, mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    diagonal_conj_simpleRootColumn]

end Algebra

variable (F : Type u) [Field F] [NumberField F]

/-- A normalized finite simple-root translation becomes a power of an integral
unipotent after conjugation by its diagonal. -/
theorem exists_conj_simpleRoot_finCol_eq_pow {r : ℕ} (i : Fin r)
    (a : Points F (r + 1)) (d : Fin (r + 1) → (FiniteAdeles F)ˣ)
    (ha : finCoord F a = diagonalMatrixUnits (FiniteAdeles F) d)
    (t : FiniteAdeles F) (ht : t ∈ integralFiniteAdeles F) (δ : ℕ) :
    ∃ g ∈ FiniteAdelicGL.standardIntegral F (r + 1),
      (finCoord F a)⁻¹ *
          finCoord F (colPoint F (j := (i : ℕ))
            (finCol F (Pi.single i.castSucc
              ((d i.castSucc : FiniteAdeles F) *
                ((d i.succ)⁻¹ : (FiniteAdeles F)ˣ) * ((δ : FiniteAdeles F) * t))))) *
          finCoord F a = g ^ δ := by
  let Y := colMatrix (i : ℕ) (Pi.single i.castSucc t)
  have hY : Y * Y = 0 := colMatrix_mul_colMatrix _ _ _
  have hYi : ∀ x y, Y x y ∈ integralFiniteAdeles F := by
    intro x y
    dsimp [Y]
    rw [colMatrix_apply]
    split_ifs
    · by_cases hx : x = i.castSucc
      · simpa [hx] using ht
      · simp [Pi.single_eq_of_ne hx]
    · exact (integralFiniteAdeles F).zero_mem
  refine ⟨sqZeroUnit Y hY, sqZeroUnit_mem_standardIntegral F Y hY hYi, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ha, finCoord_colPoint_finCol,
    diagonal_conj_one_add_simpleRootColumn, val_sqZeroUnit_pow]
  congr 1
  rw [← colMatrix_nsmul]
  congr 1
  ext x
  by_cases hx : x = i.castSucc
  · simp [hx, nsmul_eq_mul]
  · simp [Pi.single_eq_of_ne hx]

variable {r : ℕ} {V : Submodule ℂ (Points F (r + 1) → ℂ)}
    {R : ArchimedeanMatrix F (r + 1) →ₗ[ℝ] V →ₗ[ℂ] V}

/-- Nonzero Whittaker values force the character to annihilate a uniform
integral multiple of every finite simple root. -/
theorem exists_simpleRoot_finite_annihilator
    (hV : WhittakerDecayClass F r V R)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (f : V)
    {C : Set (Points F (r + 1))} (hC : IsCompact C) :
    ∃ δ : ℕ, 0 < δ ∧
      ∀ (a : Points F (r + 1)) (d : Fin (r + 1) → (FiniteAdeles F)ˣ),
        finCoord F a = diagonalMatrixUnits (FiniteAdeles F) d →
      ∀ k ∈ C, whittaker F r ψ (f : Points F (r + 1) → ℂ) (a * k) ≠ 0 →
      ∀ (i : Fin r) (t : FiniteAdeles F), t ∈ integralFiniteAdeles F →
        ψ (EqualAnalytic.finiteAdele F
          ((d i.castSucc : FiniteAdeles F) *
            ((d i.succ)⁻¹ : (FiniteAdeles F)ˣ) * ((δ : FiniteAdeles F) * t))) = 1 := by
  obtain ⟨L, hL, hfL⟩ := hV.level f
  have hQ : IsCompact (finCoord F '' C) := hC.image (continuous_finCoord F)
  obtain ⟨δ, hδ, hδL⟩ := exists_pow_conj_mem
    (FiniteAdelicGL.standardIntegral F (r + 1)).toSubgroup
    (FiniteAdelicGL.isCompact_standardIntegral F (r + 1)) L hL hQ
  refine ⟨δ, hδ, ?_⟩
  intro a d ha k hk hW i t ht
  let c : Fin (r + 1) → FiniteAdeles F := Pi.single i.castSucc
    ((d i.castSucc : FiniteAdeles F) *
      ((d i.succ)⁻¹ : (FiniteAdeles F)ˣ) * ((δ : FiniteAdeles F) * t))
  let P : Points F (r + 1) := colPoint F (j := (i : ℕ)) (finCol F c)
  obtain ⟨g, hg, hgeq⟩ := exists_conj_simpleRoot_finCol_eq_pow F i a d ha t ht δ
  change (finCoord F a)⁻¹ * finCoord F P * finCoord F a = g ^ δ at hgeq
  let l := (finCoord F (a * k))⁻¹ * finCoord F P * finCoord F (a * k)
  have hl : l ∈ L := by
    have heq : l = (finCoord F k)⁻¹ * g ^ δ * finCoord F k := by
      dsimp [l]
      rw [finCoord_mul, ← hgeq]
      simp only [mul_inv_rev, mul_assoc]
    rw [heq]
    exact hδL g hg _ ⟨k, hk, rfl⟩
  have hP : P * (a * k) = (a * k) * finitePoint F (r + 1) l := by
    dsimp [l]
    rw [← inv_mul_mul_eq_finitePoint F P (a * k)
      (infinite_colPoint_finCol F (i : ℕ) c)]
    group
  have hequiv := whittaker_colPoint_mul F ψ hψ
    (f : Points F (r + 1) → ℂ) (hV.rational f) i.is_lt (finCol F c) (a * k)
  change whittaker F r ψ (f : Points F (r + 1) → ℂ) (P * (a * k)) =
    ψ (finCol F c i.castSucc) *
      whittaker F r ψ (f : Points F (r + 1) → ℂ) (a * k) at hequiv
  rw [hP, whittaker_mul_right_of_invariant F ψ
    (f : Points F (r + 1) → ℂ) _ (fun y => hfL y l hl)] at hequiv
  have hchar := hequiv.symm
  rw [mul_eq_right₀ hW] at hchar
  simpa only [finCol, c, Pi.single_eq_same] using hchar

/-- All finite simple roots at nonzero Whittaker values have one common
rational denominator, uniformly over compact right factors. -/
theorem exists_simpleRoot_finite_denominator
    [CompactSpace (AdeleQuotient F)]
    (hV : WhittakerDecayClass F r V R)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (f : V)
    {C : Set (Points F (r + 1))} (hC : IsCompact C) :
    ∃ c : F, c ≠ 0 ∧
      ∀ (a : Points F (r + 1)) (d : Fin (r + 1) → (FiniteAdeles F)ˣ),
        finCoord F a = diagonalMatrixUnits (FiniteAdeles F) d →
      ∀ k ∈ C, whittaker F r ψ (f : Points F (r + 1) → ℂ) (a * k) ≠ 0 →
      ∀ i : Fin r, algebraMap F (FiniteAdeles F) c *
        ((d i.castSucc : FiniteAdeles F) *
          ((d i.succ)⁻¹ : (FiniteAdeles F)ˣ)) ∈ integralFiniteAdeles F := by
  obtain ⟨δ, hδ, hann⟩ := exists_simpleRoot_finite_annihilator F hV ψ hψ f hC
  obtain ⟨b, hb0, hb⟩ := EqualAnalytic.exists_eq_standardCharacter_mul F ψ hψ
  obtain ⟨D, hD0, hD⟩ := EqualAnalytic.exists_dual_denominator_finite F
  have hDF : (D : F) ≠ 0 := (Subalgebra.coe_eq_zero _).not.mpr hD0
  have hδF : (δ : F) ≠ 0 := Nat.cast_ne_zero.mpr hδ.ne'
  refine ⟨(D : F) * b * (δ : F), mul_ne_zero (mul_ne_zero hDF hb0) hδF, ?_⟩
  intro a d ha k hk hW i
  let z : FiniteAdeles F := (d i.castSucc : FiniteAdeles F) *
    ((d i.succ)⁻¹ : (FiniteAdeles F)ˣ)
  have hz : ∀ t ∈ integralFiniteAdeles F,
      adelicCharacter F (finiteToAdeles F
        ((algebraMap F (FiniteAdeles F) b * z * (δ : FiniteAdeles F)) * t)) = 1 := by
    intro t ht
    have hchar := hann a d ha k hk hW i t ht
    rw [hb, EqualAnalytic.standardCharacter_mul_finiteAdele] at hchar
    apply Circle.coe_eq_one.mp
    convert hchar using 1
    congr 3
    dsimp [z]
    ring
  have hint := hD (algebraMap F (FiniteAdeles F) b * z * (δ : FiniteAdeles F)) hz
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeles F)] at hint
  convert hint using 1
  simp only [map_mul, map_natCast]
  dsimp [z]
  ring

/-- Nonzero Whittaker values restrict every finite simple root to a fixed
compact set, uniformly over compact right factors. -/
theorem exists_simpleRoot_finite_compact_support
    [CompactSpace (AdeleQuotient F)]
    (hV : WhittakerDecayClass F r V R)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (f : V)
    {C : Set (Points F (r + 1))} (hC : IsCompact C) :
    ∃ Q : Set (FiniteAdeles F), IsCompact Q ∧
      ∀ (a : Points F (r + 1)) (d : Fin (r + 1) → (FiniteAdeles F)ˣ),
        finCoord F a = diagonalMatrixUnits (FiniteAdeles F) d →
      ∀ k ∈ C, whittaker F r ψ (f : Points F (r + 1) → ℂ) (a * k) ≠ 0 →
      ∀ i : Fin r, (d i.castSucc : FiniteAdeles F) *
        ((d i.succ)⁻¹ : (FiniteAdeles F)ˣ) ∈ Q := by
  obtain ⟨c, hc, hden⟩ := exists_simpleRoot_finite_denominator F hV ψ hψ f hC
  refine ⟨(fun y : FiniteAdeles F => algebraMap F (FiniteAdeles F) c⁻¹ * y) ''
      (integralFiniteAdeles F : Set (FiniteAdeles F)),
    (isCompact_integralFiniteAdeles F).image (continuous_const.mul continuous_id), ?_⟩
  intro a d ha k hk hW i
  refine ⟨_, hden a d ha k hk hW i, ?_⟩
  dsimp only
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]

end Langlands.Global.RankinSelbergGlobal.Unfolding
