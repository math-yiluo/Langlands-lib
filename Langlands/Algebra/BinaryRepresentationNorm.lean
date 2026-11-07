import Langlands.Algebra.BinaryDieudonne
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Matrix.Block

/-! Block-matrix determinant comparison for an actual coefficient representation. -/

noncomputable section

namespace Langlands.BinaryElementary.Representation

universe uD uR uI

variable {D : Type uD} [Ring D] {R : Type uR} [CommRing R]
  {I : Type uI} [Fintype I] [DecidableEq I]

/-- Apply a coefficient representation to the four blocks of a binary matrix. -/
def blockMap (f : D →+* Matrix I I R) :
    Matrix (Fin 2) (Fin 2) D →+* Matrix (I ⊕ I) (I ⊕ I) R where
  toFun M := Matrix.fromBlocks (f (M 0 0)) (f (M 0 1)) (f (M 1 0)) (f (M 1 1))
  map_zero' := by simp
  map_one' := by simp
  map_add' M N := by simp [Matrix.fromBlocks_add]
  map_mul' M N := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.fromBlocks_multiply]

/-- The determinant character of the coefficient representation on actual units. -/
def coefficientNorm (f : D →+* Matrix I I R) : Dˣ →* Rˣ :=
  Matrix.GeneralLinearGroup.det.comp (Units.map f.toMonoidHom)

/-- The determinant character of the represented binary matrix on actual units. -/
def binaryNorm (f : D →+* Matrix I I R) : GL₂ D →* Rˣ :=
  Matrix.GeneralLinearGroup.det.comp (Units.map (blockMap f).toMonoidHom)

@[simp] theorem coefficientNorm_val (f : D →+* Matrix I I R) (a : Dˣ) :
    (coefficientNorm f a : R) = (f (a : D)).det := rfl

@[simp] theorem binaryNorm_val (f : D →+* Matrix I I R) (g : GL₂ D) :
    (binaryNorm f g : R) = (blockMap f g.val).det := rfl

@[simp] theorem binaryNorm_upper (f : D →+* Matrix I I R) (x : D) :
    binaryNorm f (upper x) = 1 := by
  apply Units.ext
  change (blockMap f (upper x).val).det = 1
  simp [blockMap]

@[simp] theorem binaryNorm_lower (f : D →+* Matrix I I R) (x : D) :
    binaryNorm f (lower x) = 1 := by
  apply Units.ext
  change (blockMap f (lower x).val).det = 1
  simp [blockMap]

/-- Every actual elementary matrix has represented determinant one. -/
theorem elementary_le_ker (f : D →+* Matrix I I R) :
    elementary D ≤ (binaryNorm f).ker := by
  change Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  rintro g (⟨x, rfl⟩ | ⟨x, rfl⟩) <;> change binaryNorm f _ = 1 <;> simp

@[simp] theorem binaryNorm_diagonal (f : D →+* Matrix I I R) (a b : Dˣ) :
    binaryNorm f (diagonal a b) = coefficientNorm f a * coefficientNorm f b := by
  apply Units.ext
  change (blockMap f (diagonal a b).val).det = (f (a : D)).det * (f (b : D)).det
  simp [blockMap]

section DivisionRing

variable {D : Type uD} [DivisionRing D]

/-- The actual block determinant is the coefficient determinant applied to the binary determinant. -/
theorem binaryNorm_eq (f : D →+* Matrix I I R) (g : GL₂ D) :
    binaryNorm f g =
      Abelianization.lift (coefficientNorm f) (Dieudonne.determinant g) := by
  obtain ⟨e, h, a, b, he, hh, rfl⟩ := exists_elementary_diagonal_elementary g
  have hne : binaryNorm f e = 1 := elementary_le_ker f he
  have hnh : binaryNorm f h = 1 := elementary_le_ker f hh
  have hde := (Dieudonne.determinant_eq_one_iff e).mpr he
  have hdh := (Dieudonne.determinant_eq_one_iff h).mpr hh
  simp only [map_mul, hne, hnh, hde, hdh, binaryNorm_diagonal,
    Dieudonne.determinant_diagonal, one_mul, mul_one,
    Abelianization.lift_apply_of]

/-- The homomorphism-level block determinant comparison. -/
theorem binaryNorm_eq_comp (f : D →+* Matrix I I R) :
    binaryNorm f = (Abelianization.lift (coefficientNorm f)).comp
      Dieudonne.determinant :=
  MonoidHom.ext (binaryNorm_eq f)

/-- Generation of the represented norm-one group is exactly the coefficient commutator-kernel condition. -/
theorem elementary_eq_ker_iff (f : D →+* Matrix I I R) :
    elementary D = (binaryNorm f).ker ↔
      (coefficientNorm f).ker = commutator Dˣ := by
  constructor
  · intro h
    apply le_antisymm ?_ (Abelianization.commutator_subset_ker (coefficientNorm f))
    intro a ha
    apply (Dieudonne.diagonal_one_mem_iff a).mp
    rw [h]
    change binaryNorm f (diagonal a 1) = 1
    simpa only [binaryNorm_diagonal, map_one, mul_one] using
      (show coefficientNorm f a = 1 from ha)
  · intro h
    apply le_antisymm (elementary_le_ker f)
    intro g hg
    apply (Dieudonne.determinant_eq_one_iff g).mp
    have hfaithful (q : Abelianization Dˣ) :
        Abelianization.lift (coefficientNorm f) q = 1 → q = 1 := by
      refine QuotientGroup.induction_on q ?_
      intro a ha
      change a ∈ (coefficientNorm f).ker at ha
      rw [h, ← Abelianization.ker_of] at ha
      exact ha
    exact hfaithful _ ((binaryNorm_eq f g).symm.trans hg)

end DivisionRing

end Langlands.BinaryElementary.Representation
