import Langlands.Geometry.FormalGroup.CompletedUnramifiedCoefficients
import Langlands.Galois.Local.SeparableUnramifiedFrobenius
import Langlands.CommutativeAlgebra.FormallySmoothLocalCompletion

/-! # Arithmetic Frobenius on the actual completed unramified coefficients -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

open IsLocalRing ValuativeRel AdicCompletion

namespace Langlands.LocalGalois.Separable

open Langlands.CommutativeAlgebra.FormallySmoothLocalCompletion
open Langlands.GroupScheme.Descent.FiniteUnramified (fixedFieldIntegerAut)

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "C" => fixedFieldIntegers F
local notation "Ĉ" => CompletedUnramifiedIntegers F
local notation "mC" => maximalIdeal (fixedFieldIntegers F)

/-- Restrict the actual automorphism of the unramified field to its integer algebra. -/
def fixedFieldIntegerAlgAut (σ : Gal(inertiaFixedField F/F)) : C ≃ₐ[𝒪[F]] C where
  __ := fixedFieldIntegerAut F σ
  commutes' r := Subtype.ext (σ.commutes (r : F))

private theorem truncationIdeal_map (a : C ≃ₐ[𝒪[F]] C) (n : ℕ) :
    mC ^ n = (mC ^ n).map a.toRingHom := by
  rw [Ideal.map_pow]
  have hm := Ideal.comap_symm (I := mC) a.toRingEquiv
  change (mC).comap a.symm.toRingHom = (mC).map a.toRingHom at hm
  let hlocal : IsLocalHom a.symm.toRingEquiv := inferInstance
  let : IsLocalHom a.symm.toRingEquiv.toRingHom := ⟨hlocal.map_nonunit⟩
  rw [← hm, maximalIdeal_comap]

private def integerTruncationAut (a : C ≃ₐ[𝒪[F]] C) (n : ℕ) :
    (C ⧸ (mC ^ n)) ≃ₐ[𝒪[F]] C ⧸ (mC ^ n) :=
  Ideal.quotientEquivAlg _ _ a (truncationIdeal_map F a n)

private theorem integerTruncationAut_factor (a : C ≃ₐ[𝒪[F]] C) {m n : ℕ} (h : m ≤ n)
    (y : C ⧸ (mC ^ n)) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (integerTruncationAut F a n y) =
      integerTruncationAut F a m (Ideal.Quotient.factor (Ideal.pow_le_pow_right h) y) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

/-- Extend any base-linear integer automorphism to the actual adic completion. -/
def completedUnramifiedAut (a : C ≃ₐ[𝒪[F]] C) : Ĉ ≃ₐ[𝒪[F]] Ĉ :=
  adicCompletionAlgEquiv mC mC (integerTruncationAut F a) (integerTruncationAut_factor F a)

private theorem completedUnramifiedAut_eval (a : C ≃ₐ[𝒪[F]] C) (n : ℕ) (x : Ĉ) :
    evalₐ mC n (completedUnramifiedAut F a x) = integerTruncationAut F a n (evalₐ mC n x) := by
  unfold completedUnramifiedAut adicCompletionAlgEquiv
  erw [evalₐ_liftAlgHom (R := 𝒪[F])]
  · rfl
  · intro m k h
    apply AlgHom.ext
    intro y
    exact (integerTruncationAut_factor F a h (evalₐ mC k y)).trans
      (congrArg (integerTruncationAut F a m) (factor_evalₐ mC h y))

/-- The lift restricts to the given automorphism on the embedded integers. -/
theorem completedUnramifiedAut_onIntegers (a : C ≃ₐ[𝒪[F]] C) (x : C) :
    completedUnramifiedAut F a (toCompletedUnramifiedIntegers F x) =
      toCompletedUnramifiedIntegers F (a x) := by
  apply ext_evalₐ
  intro n
  rw [completedUnramifiedAut_eval]
  change integerTruncationAut F a n (evalₐ mC n (of mC C x)) = evalₐ mC n (of mC C (a x))
  rw [evalₐ_of, evalₐ_of]
  rfl

private theorem completedUnramifiedReduction_eq_evalOne (x : Ĉ) :
    completedUnramifiedReduction F x = evalOneₐ mC x := by
  obtain ⟨y, hy⟩ := residue_surjective (R := C) (evalOneₐ mC x)
  have he : evalOneₐ mC (x - toCompletedUnramifiedIntegers F y) = 0 := by
    rw [map_sub]
    change evalOneₐ mC x - evalOneₐ mC (of mC C y) = 0
    rw [evalOneₐ_of]
    exact sub_eq_zero.mpr hy.symm
  have hx : x - toCompletedUnramifiedIntegers F y ∈ maximalIdeal Ĉ := by
    rw [AdicCompletion.maximalIdeal_eq_map, ← ker_evalOneₐ_eq_map mC (mC).fg_of_isNoetherianRing]
    exact he
  have hres : residue Ĉ x = residue Ĉ (toCompletedUnramifiedIntegers F y) := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hx
  change completedUnramifiedResidueEquiv F (residue Ĉ x) = _
  rw [hres, completedUnramifiedResidueEquiv_residue, hy]

/-- The lifted automorphism reduces to the induced automorphism of the actual
unramified residue field. -/
theorem completedUnramifiedAut_reduction (a : C ≃ₐ[𝒪[F]] C) (x : Ĉ) :
    completedUnramifiedReduction F (completedUnramifiedAut F a x) =
      ResidueField.mapAlgEquiv a (completedUnramifiedReduction F x) := by
  rw [completedUnramifiedReduction_eq_evalOne, completedUnramifiedReduction_eq_evalOne]
  simp only [evalOneₐ, AlgHom.comp_apply, completedUnramifiedAut_eval]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ mC 1 x)
  rw [← hy]
  rfl

/-- Arithmetic Frobenius on the completed unramified base, obtained by extending
the actual arithmetic Frobenius of the separable inertia fixed field. -/
def completedUnramifiedFrobenius : Ĉ ≃ₐ[𝒪[F]] Ĉ :=
  completedUnramifiedAut F (fixedFieldIntegerAlgAut F (exists_fixedField_arithmeticFrobenius F).choose)

/-- Arithmetic Frobenius is the residue-cardinality power on the completed base's residue. -/
theorem completedUnramifiedFrobenius_reduction (x : Ĉ) :
    completedUnramifiedReduction F (completedUnramifiedFrobenius F x) =
      (completedUnramifiedReduction F x) ^ Nat.card 𝓀[F] := by
  rw [completedUnramifiedFrobenius, completedUnramifiedAut_reduction]
  obtain ⟨y, hy⟩ := residue_surjective (R := C) (completedUnramifiedReduction F x)
  rw [← hy, ResidueField.mapAlgEquiv_residue]
  exact (exists_fixedField_arithmeticFrobenius F).choose_spec.2 y

end Langlands.LocalGalois.Separable
