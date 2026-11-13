import Langlands.LinearAlgebra.SpecialLinearConjugationScalars
import Langlands.LinearAlgebra.SpecialLinearHermitianNormalization
import Mathlib.FieldTheory.Galois.Basic

/-! # Descent of a projectively fixed conjugating matrix -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w t

namespace Langlands.LinearAlgebra.SpecialLinearProjectiveDescent

open Matrix
open Langlands.LinearAlgebra.SpecialLinearConjugation
open Langlands.LinearAlgebra.SpecialLinearHermitianNormalization

variable {I : Type u} [Fintype I] [DecidableEq I]
  {M : Type v} [Field M]

/-- Divide an invertible matrix by any specified nonzero entry. -/
def normalizeEntry (X : GeneralLinearGroup I M) (p q : I) (hpq : X p q ≠ 0) :
    GeneralLinearGroup I M :=
  GeneralLinearGroup.scalar I ((Units.mk0 (X p q) hpq)⁻¹) * X

/-- The entry used for normalization becomes one; it need not be diagonal. -/
theorem normalizeEntry_entry (X : GeneralLinearGroup I M) (p q : I) (hpq : X p q ≠ 0) :
    normalizeEntry X p q hpq p q = 1 := by
  simp only [normalizeEntry, Units.val_mul, GeneralLinearGroup.coe_scalar,
    Units.val_inv_eq_inv_val, Units.val_mk0, Matrix.scalar_apply, Matrix.diagonal_mul]
  exact inv_mul_cancel₀ hpq

/-- Entry normalization preserves conjugation after every coefficient homomorphism. -/
theorem normalizeEntry_conjugate {R : Type w} [CommRing R] (f : M →+* R)
    (X : GeneralLinearGroup I M) (p q : I) (hpq : X p q ≠ 0)
    (g : GeneralLinearGroup I R) :
    GeneralLinearGroup.map f (normalizeEntry X p q hpq) * g *
        (GeneralLinearGroup.map f (normalizeEntry X p q hpq))⁻¹ =
      GeneralLinearGroup.map f X * g * (GeneralLinearGroup.map f X)⁻¹ :=
  map_scalar_mul_conjugate f _ X g

/-- Normalization at an arbitrary entry removes the scalar ambiguity of an `SL` action. -/
theorem eq_of_conjugation_eq_of_entry_eq_one
    (X Y : GeneralLinearGroup I M) (p q : I)
    (hX : X p q = 1) (hY : Y p q = 1)
    (h : ∀ g : SpecialLinearGroup I M,
      X * SpecialLinearGroup.toGL g * X⁻¹ =
        Y * SpecialLinearGroup.toGL g * Y⁻¹) : X = Y := by
  obtain ⟨b, hb⟩ := exists_unit_scalar_of_conjugation_eq_conjugation X Y h
  have he := congrArg (fun Q : GeneralLinearGroup I M => Q p q) hb
  have hb1 : (b : M) = 1 := by
    simpa [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.mul_diagonal, hX, hY] using he.symm
  have hbu : b = 1 := Units.ext hb1
  simpa only [hbu, map_one, mul_one] using hb

variable {K : Type t} [Field K] [Algebra K M]
  (H : Subgroup (M ≃ₐ[K] M))

/-- A matrix fixed projectively on `SL` becomes exactly fixed after entry normalization. -/
theorem normalizeEntry_fixed (X : GeneralLinearGroup I M) (p q : I) (hpq : X p q ≠ 0)
    (hX : ∀ (σ : H) (g : SpecialLinearGroup I M),
      GeneralLinearGroup.map σ.val.toRingHom X * SpecialLinearGroup.toGL g *
          (GeneralLinearGroup.map σ.val.toRingHom X)⁻¹ =
        X * SpecialLinearGroup.toGL g * X⁻¹)
    (σ : H) :
    GeneralLinearGroup.map σ.val.toRingHom (normalizeEntry X p q hpq) =
      normalizeEntry X p q hpq := by
  apply eq_of_conjugation_eq_of_entry_eq_one _ _ p q
  · change σ.val (normalizeEntry X p q hpq p q) = 1
    rw [normalizeEntry_entry, map_one]
  · exact normalizeEntry_entry X p q hpq
  · intro g
    calc
      _ = GeneralLinearGroup.map σ.val.toRingHom X * SpecialLinearGroup.toGL g *
          (GeneralLinearGroup.map σ.val.toRingHom X)⁻¹ :=
        normalizeEntry_conjugate σ.val.toRingHom X p q hpq _
      _ = X * SpecialLinearGroup.toGL g * X⁻¹ := hX σ g
      _ = _ := (normalizeEntry_conjugate (RingHom.id M) X p q hpq _).symm

variable {L : Type w} [Field L]

omit H [Algebra K M] [Field K] in
/-- Coefficientwise mapping into a field is injective on invertible matrices. -/
theorem mapGL_injective (f : L →+* M) :
    Function.Injective (GeneralLinearGroup.map (n := I) f) := by
  intro X Y h
  apply Units.ext
  ext i j
  apply f.injective
  exact congrArg (fun Q : GeneralLinearGroup I M => Q i j) h

/-- An exactly fixed matrix descends whenever every fixed coefficient does. -/
theorem exists_matrix_of_fixed (f : L →+* M)
    (hf : ∀ x : M, (∀ σ : H, σ.val x = x) → ∃ y : L, f y = x)
    (X : GeneralLinearGroup I M)
    (hX : ∀ σ : H, GeneralLinearGroup.map σ.val.toRingHom X = X) :
    ∃ Y : GeneralLinearGroup I L, GeneralLinearGroup.map f Y = X := by
  choose A hA using fun i j : I => hf (X i j) (fun σ =>
    congrArg (fun Q : GeneralLinearGroup I M => Q i j) (hX σ))
  have hAm : Matrix.map A f = X.val := by
    ext i j
    exact hA i j
  have hdet : Matrix.det A ≠ 0 := by
    intro hz
    apply X.det_ne_zero
    rw [← hAm]
    change (f.mapMatrix (A : Matrix I I L)).det = 0
    rw [← f.map_det, hz, map_zero]
  refine ⟨GeneralLinearGroup.mkOfDetNeZero A hdet, ?_⟩
  apply Units.ext
  exact hAm

/-- A projectively fixed matrix descends up to a scalar, over any nonempty finite index type. -/
theorem exists_projective_descent [Nonempty I] (f : L →+* M)
    (hf : ∀ x : M, (∀ σ : H, σ.val x = x) → ∃ y : L, f y = x)
    (X : GeneralLinearGroup I M)
    (hX : ∀ (σ : H) (g : SpecialLinearGroup I M),
      GeneralLinearGroup.map σ.val.toRingHom X * SpecialLinearGroup.toGL g *
          (GeneralLinearGroup.map σ.val.toRingHom X)⁻¹ =
        X * SpecialLinearGroup.toGL g * X⁻¹) :
    ∃ (Y : GeneralLinearGroup I L) (b : Mˣ),
      GeneralLinearGroup.map f Y = GeneralLinearGroup.scalar I b * X := by
  have hnz : ∃ p q : I, X p q ≠ 0 := by
    by_contra! h
    apply Units.ne_zero X
    ext i j
    exact h i j
  obtain ⟨p, q, hpq⟩ := hnz
  obtain ⟨Y, hY⟩ := exists_matrix_of_fixed H f hf (normalizeEntry X p q hpq)
    (normalizeEntry_fixed H X p q hpq hX)
  exact ⟨Y, (Units.mk0 (X p q) hpq)⁻¹, hY⟩

omit H in
/-- In a finite Galois extension, the coefficients fixed by a range-fixing subgroup
are precisely the image of that field embedding. -/
theorem exists_preimage_of_fixed [Algebra K L] [FiniteDimensional K M] [IsGalois K M]
    (f : L →ₐ[K] M) (x : M)
    (hx : ∀ σ : f.fieldRange.fixingSubgroup, σ.val x = x) :
    ∃ y : L, f y = x := by
  apply f.mem_fieldRange.mp
  rw [← IsGalois.fixedField_fixingSubgroup f.fieldRange]
  rw [IntermediateField.mem_fixedField_iff]
  exact fun σ hσ => hx ⟨σ, hσ⟩

omit H in
/-- Finite Galois descent of a conjugating matrix up to a scalar. -/
theorem exists_projective_descent_galois [Nonempty I] [Algebra K L]
    [FiniteDimensional K M] [IsGalois K M] (f : L →ₐ[K] M)
    (X : GeneralLinearGroup I M)
    (hX : ∀ (σ : f.fieldRange.fixingSubgroup) (g : SpecialLinearGroup I M),
      GeneralLinearGroup.map σ.val.toRingHom X * SpecialLinearGroup.toGL g *
          (GeneralLinearGroup.map σ.val.toRingHom X)⁻¹ =
        X * SpecialLinearGroup.toGL g * X⁻¹) :
    ∃ (Y : GeneralLinearGroup I L) (b : Mˣ),
      GeneralLinearGroup.map f.toRingHom Y = GeneralLinearGroup.scalar I b * X :=
  exists_projective_descent f.fieldRange.fixingSubgroup f.toRingHom
    (exists_preimage_of_fixed f) X hX

omit H [Algebra K M] [Field K] in
/-- Being a unit scalar is reflected by an embedding of coefficient fields. -/
theorem exists_scalar_of_map_eq_scalar [Nonempty I] (f : L →+* M)
    (X : GeneralLinearGroup I L) (b : Mˣ)
    (hX : GeneralLinearGroup.map f X = GeneralLinearGroup.scalar I b) :
    ∃ a : Lˣ, X = GeneralLinearGroup.scalar I a := by
  let p : I := Classical.choice inferInstance
  have he : f (X p p) = (b : M) := by
    simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using
      congrArg (fun Q : GeneralLinearGroup I M => Q p p) hX
  have hn : X p p ≠ 0 := by
    intro hz
    rw [hz, map_zero] at he
    exact b.ne_zero he.symm
  let a := Units.mk0 (X p p) hn
  have ha : Units.map f.toMonoidHom a = b := Units.ext he
  refine ⟨a, mapGL_injective f ?_⟩
  rw [GeneralLinearGroup.map_scalar]
  change GeneralLinearGroup.map f X = GeneralLinearGroup.scalar I (Units.map f.toMonoidHom a)
  rw [ha]
  exact hX

end Langlands.LinearAlgebra.SpecialLinearProjectiveDescent
