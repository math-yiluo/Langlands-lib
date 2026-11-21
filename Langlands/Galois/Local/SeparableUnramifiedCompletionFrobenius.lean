import Langlands.CommutativeAlgebra.FormallySmoothLocalCompletion
import Langlands.Galois.Local.SeparableUnramifiedCompletion
import Langlands.Galois.Local.SeparableUnramifiedFrobenius

/-! # Arithmetic Frobenius on the completed maximal unramified integers -/

noncomputable section

open IsLocalRing ValuativeRel AdicCompletion

namespace Langlands.LocalGalois.Separable.UnramifiedCompletion

open Langlands.CommutativeAlgebra.FormallySmoothLocalCompletion
open Langlands.GroupScheme.Descent.FiniteUnramified (fixedFieldIntegerAut)

universe u

section Completion

variable {S : Type u} [CommRing S] [IsLocalRing S]

private def truncAut (e : S ≃+* S) (n : ℕ) :
    (S ⧸ maximalIdeal S ^ n) ≃ₐ[ℤ] (S ⧸ maximalIdeal S ^ n) :=
  Ideal.quotientEquivAlg (maximalIdeal S ^ n) (J := maximalIdeal S ^ n) e.toIntAlgEquiv (by
    change maximalIdeal S ^ n = (maximalIdeal S ^ n).map e
    rw [Ideal.map_pow, map_ringEquiv_maximalIdeal])

private theorem truncAut_compatible (e : S ≃+* S) {m n : ℕ} (h : m ≤ n)
    (x : S ⧸ maximalIdeal S ^ n) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (truncAut e n x) =
      truncAut e m (Ideal.Quotient.factor (Ideal.pow_le_pow_right h) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- Extend a local ring automorphism through the compatible automorphisms of
all maximal-ideal power quotients. -/
def completeLocalRingAut (e : S ≃+* S) :
    AdicCompletion (maximalIdeal S) S ≃+* AdicCompletion (maximalIdeal S) S :=
  (adicCompletionAlgEquiv (maximalIdeal S) (maximalIdeal S)
    (truncAut e) (truncAut_compatible e)).toRingEquiv

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem completeLocalRingAut_algebraMap (e : S ≃+* S) (x : S) :
    completeLocalRingAut e (algebraMap S (AdicCompletion (maximalIdeal S) S) x) =
      algebraMap S _ (e x) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  change evalₐ (maximalIdeal S) n
      (completeLocalRingAut e (AdicCompletion.of (maximalIdeal S) S x)) =
    evalₐ (maximalIdeal S) n (AdicCompletion.of (maximalIdeal S) S (e x))
  rw [show evalₐ (maximalIdeal S) n
      (completeLocalRingAut e (AdicCompletion.of (maximalIdeal S) S x)) =
      truncAut e n (evalₐ (maximalIdeal S) n (AdicCompletion.of (maximalIdeal S) S x)) by
    simp only [completeLocalRingAut, adicCompletionAlgEquiv, AlgEquiv.coe_ringEquiv,
      AlgEquiv.ofAlgHom_apply]
    apply evalₐ_liftAlgHom
    intro m k h
    apply AlgHom.ext
    intro y
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Ideal.Quotient.factorₐ_apply]
    exact (truncAut_compatible e h _).trans
      (congrArg (truncAut e m) (factor_evalₐ (maximalIdeal S) h y))]
  rw [evalₐ_of, evalₐ_of]
  rfl

end Completion

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Extend the actual field automorphism on inertia-fixed integers to the
completion, fixing the original integer ring. -/
def integerAut (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    Integers F ≃ₐ[𝒪[F]] Integers F where
  __ := completeLocalRingAut (fixedFieldIntegerAut F σ)
  commutes' r := by
    change completeLocalRingAut (fixedFieldIntegerAut F σ)
      (algebraMap (fixedFieldIntegers F) (Integers F) (integerToFixedField F r)) = _
    rw [completeLocalRingAut_algebraMap]
    exact congrArg (algebraMap (fixedFieldIntegers F) (Integers F))
      (Subtype.ext (σ.commutes (r : F)))

@[simp]
theorem integerAut_algebraMap (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (x : fixedFieldIntegers F) :
    integerAut F σ (algebraMap (fixedFieldIntegers F) (Integers F) x) =
      algebraMap (fixedFieldIntegers F) (Integers F) (fixedFieldIntegerAut F σ x) :=
  completeLocalRingAut_algebraMap (fixedFieldIntegerAut F σ) x

/-- Arithmetic Frobenius on the actual completed maximal unramified integers. -/
def arithmeticFrobenius : Integers F ≃ₐ[𝒪[F]] Integers F :=
  integerAut F (exists_fixedField_arithmeticFrobenius F).choose

/-- The completed lift acts by the scalar residue cardinal power on the whole residue field. -/
theorem residue_arithmeticFrobenius (x : Integers F) :
    residue (Integers F) (arithmeticFrobenius F x) =
      residue (Integers F) x ^ Nat.card 𝓀[F] := by
  obtain ⟨y, hy⟩ := (residueEquiv F).surjective (residue (Integers F) x)
  obtain ⟨r, rfl⟩ := residue_surjective y
  have h : residue (Integers F) (algebraMap (fixedFieldIntegers F) (Integers F) r) =
      residue (Integers F) x := (residueEquiv_residue F r).symm.trans hy
  have hσ := congrArg (ResidueField.mapEquiv (arithmeticFrobenius F).toRingEquiv) h
  simp only [ResidueField.mapEquiv_apply, ResidueField.map_residue] at hσ
  refine hσ.symm.trans ?_
  rw [← h]
  change residue (Integers F) (integerAut F _ (algebraMap _ _ r)) = _
  rw [integerAut_algebraMap, ← residueEquiv_residue, ← residueEquiv_residue,
    (exists_fixedField_arithmeticFrobenius F).choose_spec.2 r, map_pow]

end Langlands.LocalGalois.Separable.UnramifiedCompletion
