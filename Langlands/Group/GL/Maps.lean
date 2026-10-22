import Langlands.Group.GL.Padic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.Rev

/-!
# Permutation matrices and inverse transpose on the general linear group

All groups below are the actual Mathlib groups of invertible matrices, exposed
by `Langlands.Group.GL.Basic`. The final section specializes the constructions
to every supplied and canonical p-adic field topology.
-/

namespace Langlands.GeneralLinear

universe u

variable (n : ℕ) (R : Type u) [CommRing R]

/-- The permutation matrix sending the standard basis vector `e j` to `e (σ j)`. -/
def permutation : Equiv.Perm (Fin n) →* Matrix.GeneralLinearGroup (Fin n) R :=
  Matrix.permMatrixHom.toHomUnits

@[simp]
theorem permutation_coe (σ : Equiv.Perm (Fin n)) :
    (permutation n R σ : Matrix (Fin n) (Fin n) R) = σ⁻¹.permMatrix R :=
  rfl

theorem permutation_entry (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    permutation n R σ i j = if σ j = i then 1 else 0 := by
  change (σ⁻¹).permMatrix R i j = _
  simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  change (if σ.symm i = j then (1 : R) else 0) = _
  simp only [σ.symm_apply_eq, eq_comm]

@[simp]
theorem permutation_inv (σ : Equiv.Perm (Fin n)) :
    (permutation n R σ)⁻¹ = permutation n R σ⁻¹ :=
  (map_inv (permutation n R) σ).symm

theorem permutation_mul_entry (σ : Equiv.Perm (Fin n))
    (g : Matrix.GeneralLinearGroup (Fin n) R) (i j : Fin n) :
    (permutation n R σ * g) i j = g (σ⁻¹ i) j := by
  change (((σ⁻¹).toPEquiv.toMatrix : Matrix (Fin n) (Fin n) R) *
    (g : Matrix (Fin n) (Fin n) R)) i j = _
  rw [PEquiv.toMatrix_toPEquiv_mul]
  rfl

theorem mul_permutation_entry (g : Matrix.GeneralLinearGroup (Fin n) R)
    (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (g * permutation n R σ) i j = g i (σ j) := by
  change ((g : Matrix (Fin n) (Fin n) R) *
    ((σ⁻¹).toPEquiv.toMatrix : Matrix (Fin n) (Fin n) R)) i j = _
  rw [PEquiv.mul_toMatrix_toPEquiv]
  rfl

theorem permutation_conjugate_entry (σ : Equiv.Perm (Fin n))
    (g : Matrix.GeneralLinearGroup (Fin n) R) (i j : Fin n) :
    (permutation n R σ * g * (permutation n R σ)⁻¹) i j =
      g (σ⁻¹ i) (σ⁻¹ j) := by
  rw [permutation_inv, mul_permutation_entry, permutation_mul_entry]

/-- The long Weyl representative with ones on the anti-diagonal. -/
def weylLong : Matrix.GeneralLinearGroup (Fin n) R :=
  permutation n R Fin.revPerm

theorem weylLong_entry (i j : Fin n) :
    weylLong n R i j = if j.rev = i then 1 else 0 := by
  simpa [weylLong] using permutation_entry n R Fin.revPerm i j

@[simp]
theorem weylLong_inv : (weylLong n R)⁻¹ = weylLong n R := by
  rw [weylLong, permutation_inv]
  rfl

@[simp]
theorem weylLong_mul_self : weylLong n R * weylLong n R = 1 := by
  rw [← weylLong_inv n R]
  exact inv_mul_cancel _

theorem weylLong_mul_entry (g : Matrix.GeneralLinearGroup (Fin n) R)
    (i j : Fin n) :
    (weylLong n R * g) i j = g i.rev j := by
  exact permutation_mul_entry n R Fin.revPerm g i j

theorem mul_weylLong_entry (g : Matrix.GeneralLinearGroup (Fin n) R)
    (i j : Fin n) :
    (g * weylLong n R) i j = g i j.rev := by
  exact mul_permutation_entry n R g Fin.revPerm i j

theorem weylLong_conjugate_entry (g : Matrix.GeneralLinearGroup (Fin n) R)
    (i j : Fin n) :
    (weylLong n R * g * weylLong n R) i j = g i.rev j.rev := by
  rw [mul_weylLong_entry, weylLong_mul_entry]

/-- The involutive automorphism `g ↦ (g⁻¹)ᵀ`, including its intrinsic group laws. -/
def inverseTranspose :
    Matrix.GeneralLinearGroup (Fin n) R ≃* Matrix.GeneralLinearGroup (Fin n) R :=
  let f : Matrix.GeneralLinearGroup (Fin n) R → Matrix.GeneralLinearGroup (Fin n) R :=
    fun g =>
      { val := g.inv.transpose
        inv := g.val.transpose
        val_inv := by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]
        inv_val := by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one] }
  { toFun := f
    invFun := f
    left_inv := by intro g; apply Units.ext; rfl
    right_inv := by intro g; apply Units.ext; rfl
    map_mul' := by
      intro g h
      apply Units.ext
      change ((h⁻¹ : Matrix.GeneralLinearGroup (Fin n) R).val *
        (g⁻¹ : Matrix.GeneralLinearGroup (Fin n) R).val).transpose = _
      exact Matrix.transpose_mul _ _ }

@[simp]
theorem inverseTranspose_coe (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (inverseTranspose n R g : Matrix (Fin n) (Fin n) R) =
      (g⁻¹ : Matrix.GeneralLinearGroup (Fin n) R).val.transpose :=
  rfl

@[simp]
theorem inverseTranspose_entry (g : Matrix.GeneralLinearGroup (Fin n) R)
    (i j : Fin n) :
    inverseTranspose n R g i j = g⁻¹ j i :=
  rfl

@[simp]
theorem inverseTranspose_symm : (inverseTranspose n R).symm = inverseTranspose n R :=
  rfl

@[simp]
theorem inverseTranspose_involutive (g : Matrix.GeneralLinearGroup (Fin n) R) :
    inverseTranspose n R (inverseTranspose n R g) = g :=
  (inverseTranspose n R).left_inv g

@[simp]
theorem inverseTranspose_permutation (σ : Equiv.Perm (Fin n)) :
    inverseTranspose n R (permutation n R σ) = permutation n R σ := by
  apply Units.ext
  simp only [inverseTranspose_coe, permutation_inv, permutation_coe,
    Matrix.transpose_permMatrix, inv_inv]

@[simp]
theorem inverseTranspose_weylLong :
    inverseTranspose n R (weylLong n R) = weylLong n R :=
  inverseTranspose_permutation n R Fin.revPerm

variable [TopologicalSpace R]

/-- Inverse transpose is continuous for the existing Mathlib units topology. -/
@[fun_prop]
theorem continuous_inverseTranspose :
    Continuous (inverseTranspose n R) :=
  Units.continuous_iff.mpr
    ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

/-- Inverse transpose as a continuous group automorphism. -/
def inverseTransposeContinuous :
    Matrix.GeneralLinearGroup (Fin n) R ≃ₜ* Matrix.GeneralLinearGroup (Fin n) R where
  toMulEquiv := inverseTranspose n R
  continuous_toFun := continuous_inverseTranspose n R
  continuous_invFun := continuous_inverseTranspose n R

@[simp]
theorem inverseTransposeContinuous_apply (g : Matrix.GeneralLinearGroup (Fin n) R) :
    inverseTransposeContinuous n R g = inverseTranspose n R g :=
  rfl

variable [IsTopologicalRing R]

/-- Permutation conjugation as a continuous group automorphism. -/
def permutationConjugation (σ : Equiv.Perm (Fin n)) :
    Matrix.GeneralLinearGroup (Fin n) R ≃ₜ* Matrix.GeneralLinearGroup (Fin n) R where
  toMulEquiv := MulAut.conj (permutation n R σ)
  continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
  continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const

@[simp]
theorem permutationConjugation_apply (σ : Equiv.Perm (Fin n))
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    permutationConjugation n R σ g =
      permutation n R σ * g * (permutation n R σ)⁻¹ :=
  rfl

theorem permutationConjugation_entry (σ : Equiv.Perm (Fin n))
    (g : Matrix.GeneralLinearGroup (Fin n) R) (i j : Fin n) :
    permutationConjugation n R σ g i j = g (σ⁻¹ i) (σ⁻¹ j) :=
  permutation_conjugate_entry n R σ g i j

/-- The homeomorphism `g ↦ wₙ (g⁻¹)ᵀ` occurring in the Whittaker convention.
It is a homeomorphism of spaces, not an asserted group homomorphism. -/
def weylInverseTranspose :
    Matrix.GeneralLinearGroup (Fin n) R ≃ₜ Matrix.GeneralLinearGroup (Fin n) R :=
  (inverseTransposeContinuous n R).toHomeomorph.trans (Homeomorph.mulLeft (weylLong n R))

@[simp]
theorem weylInverseTranspose_apply (g : Matrix.GeneralLinearGroup (Fin n) R) :
    weylInverseTranspose n R g = weylLong n R * inverseTranspose n R g :=
  rfl

theorem weylInverseTranspose_entry (g : Matrix.GeneralLinearGroup (Fin n) R)
    (i j : Fin n) :
    weylInverseTranspose n R g i j = g⁻¹ j i.rev := by
  rw [weylInverseTranspose_apply, weylLong_mul_entry, inverseTranspose_entry]

@[simp]
theorem weylInverseTranspose_involutive (g : Matrix.GeneralLinearGroup (Fin n) R) :
    weylInverseTranspose n R (weylInverseTranspose n R g) = g := by
  simp only [weylInverseTranspose_apply, map_mul, inverseTranspose_weylLong,
    inverseTranspose_involutive, ← mul_assoc, weylLong_mul_self, one_mul]

end Langlands.GeneralLinear

namespace Langlands.PadicField

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}

namespace TopologicalData

/-- Inverse transpose for the selected topology of a p-adic field. -/
def generalLinearInverseTranspose (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    GeneralLinear n F.Carrier ≃ₜ* GeneralLinear n F.Carrier := by
  letI := T.topology
  exact GeneralLinear.inverseTransposeContinuous n F.Carrier

/-- Permutation conjugation for the selected topology of a p-adic field. -/
def generalLinearPermutationConjugation (T : F.TopologicalData) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    letI := T.topology
    GeneralLinear n F.Carrier ≃ₜ* GeneralLinear n F.Carrier := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact GeneralLinear.permutationConjugation n F.Carrier σ

/-- The Weyl--inverse-transpose homeomorphism for a selected field topology. -/
def generalLinearWeylInverseTranspose (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    GeneralLinear n F.Carrier ≃ₜ GeneralLinear n F.Carrier := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact GeneralLinear.weylInverseTranspose n F.Carrier

end TopologicalData

/-- Canonical continuous inverse transpose on every finite p-adic extension. -/
noncomputable abbrev canonicalGeneralLinearInverseTranspose
    (F : PadicField.{u} p) (n : ℕ) :
    letI := F.canonicalTopologicalData.topology
    GeneralLinear n F.Carrier ≃ₜ* GeneralLinear n F.Carrier :=
  F.canonicalTopologicalData.generalLinearInverseTranspose n

/-- Canonical continuous permutation conjugation on every finite p-adic extension. -/
noncomputable abbrev canonicalGeneralLinearPermutationConjugation
    (F : PadicField.{u} p) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    letI := F.canonicalTopologicalData.topology
    GeneralLinear n F.Carrier ≃ₜ* GeneralLinear n F.Carrier :=
  F.canonicalTopologicalData.generalLinearPermutationConjugation n σ

/-- Canonical Weyl--inverse-transpose homeomorphism on every finite p-adic extension. -/
noncomputable abbrev canonicalGeneralLinearWeylInverseTranspose
    (F : PadicField.{u} p) (n : ℕ) :
    letI := F.canonicalTopologicalData.topology
    GeneralLinear n F.Carrier ≃ₜ GeneralLinear n F.Carrier :=
  F.canonicalTopologicalData.generalLinearWeylInverseTranspose n

end Langlands.PadicField
