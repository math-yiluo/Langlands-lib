import Langlands.Algebra.FilteredSymmetricAlgebraSymmetrization

/-! # Filtered product comparison for whole symmetrization -/

noncomputable section
universe v
set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type) (L : Type v) [Field R] [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "S" => SymmetricAlgebra R L

/-- The bilinear error between symmetrizing a product and multiplying the
symmetrized factors. -/
def symmetricAlgebraSymmetrizeMultiplicationError : S →ₗ[R] S →ₗ[R] U :=
  LinearMap.mk₂ R
    (fun P Q => symmetricAlgebraSymmetrize R L (P * Q) -
      symmetricAlgebraSymmetrize R L P * symmetricAlgebraSymmetrize R L Q)
    (by intros; simp only [add_mul, map_add, add_sub_add_comm])
    (by intros; simp only [smul_mul_assoc, map_smul, smul_sub])
    (by intros; simp only [mul_add, map_add, add_sub_add_comm])
    (by intros; simp only [mul_smul_comm, map_smul, smul_sub])

@[simp] theorem symmetricAlgebraSymmetrizeMultiplicationError_apply (P Q : S) :
    symmetricAlgebraSymmetrizeMultiplicationError R L P Q =
      symmetricAlgebraSymmetrize R L (P * Q) -
        symmetricAlgebraSymmetrize R L P * symmetricAlgebraSymmetrize R L Q := rfl

variable [CharZero R]

/-- Multiplying two actual symmetric monomials agrees with multiplying their
symmetrizations up to a strict lower-degree enveloping error. -/
theorem symmetricAlgebraSymmetrize_prod_mul_sub_mem (l m : List L) :
    symmetricAlgebraSymmetrize R L
        ((l.map (SymmetricAlgebra.ι R L)).prod *
          (m.map (SymmetricAlgebra.ι R L)).prod) -
      symmetricAlgebraSymmetrize R L ((l.map (SymmetricAlgebra.ι R L)).prod) *
        symmetricAlgebraSymmetrize R L ((m.map (SymmetricAlgebra.ι R L)).prod) ∈
      degreeFiltration R L (l.length + m.length - 1) := by
  cases l with
  | nil => simp
  | cons x l =>
    cases m with
    | nil => simp
    | cons y m =>
      have hconcat :
          symmetricAlgebraSymmetrize R L
              (((x :: l).map (SymmetricAlgebra.ι R L)).prod *
                ((y :: m).map (SymmetricAlgebra.ι R L)).prod) -
            word R L (x :: l) * word R L (y :: m) ∈
          degreeFiltration R L ((x :: l).length + (y :: m).length - 1) := by
        simpa only [List.map_append, List.prod_append, List.length_append, word] using
          symmetricAlgebraSymmetrize_prod_sub_word_mem R L ((x :: l) ++ (y :: m))
      have hleft := mul_mem_degreeFiltration R L
        (symmetricAlgebraSymmetrize_prod_sub_word_mem R L (x :: l))
        (symmetricAlgebraSymmetrize_prod_mem R L (y :: m))
      have hright := mul_mem_degreeFiltration R L
        (word_mem_degreeFiltration R L (x :: l))
        (symmetricAlgebraSymmetrize_prod_sub_word_mem R L (y :: m))
      have hdegLeft :
          (x :: l).length - 1 + (y :: m).length =
            (x :: l).length + (y :: m).length - 1 := by
        simp only [List.length_cons]
        omega
      have hdegRight :
          (x :: l).length + ((y :: m).length - 1) =
            (x :: l).length + (y :: m).length - 1 := by
        simp only [List.length_cons]
        omega
      rw [hdegLeft] at hleft
      rw [hdegRight] at hright
      have heq :
          symmetricAlgebraSymmetrize R L
              (((x :: l).map (SymmetricAlgebra.ι R L)).prod *
                ((y :: m).map (SymmetricAlgebra.ι R L)).prod) -
            symmetricAlgebraSymmetrize R L (((x :: l).map (SymmetricAlgebra.ι R L)).prod) *
              symmetricAlgebraSymmetrize R L (((y :: m).map (SymmetricAlgebra.ι R L)).prod) =
          (symmetricAlgebraSymmetrize R L
              (((x :: l).map (SymmetricAlgebra.ι R L)).prod *
                ((y :: m).map (SymmetricAlgebra.ι R L)).prod) -
            word R L (x :: l) * word R L (y :: m)) -
          ((symmetricAlgebraSymmetrize R L
                (((x :: l).map (SymmetricAlgebra.ι R L)).prod) - word R L (x :: l)) *
              symmetricAlgebraSymmetrize R L (((y :: m).map (SymmetricAlgebra.ι R L)).prod) +
            word R L (x :: l) *
              (symmetricAlgebraSymmetrize R L
                (((y :: m).map (SymmetricAlgebra.ι R L)).prod) - word R L (y :: m))) := by
        noncomm_ring
      rw [heq]
      exact (degreeFiltration R L _).sub_mem hconcat
        ((degreeFiltration R L _).add_mem hleft hright)

/-- Whole symmetrization is multiplicative modulo the strict lower-degree
piece on any two bounded symmetric spans. -/
theorem symmetricAlgebraSymmetrize_mul_sub_mem {p q : ℕ} {P Q : S}
    (hP : P ∈ symmetricDegreeFiltration R L p)
    (hQ : Q ∈ symmetricDegreeFiltration R L q) :
    symmetricAlgebraSymmetrize R L (P * Q) -
      symmetricAlgebraSymmetrize R L P * symmetricAlgebraSymmetrize R L Q ∈
        degreeFiltration R L (p + q - 1) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨m, hm, rfl⟩ := hQ
      exact degreeFiltration_mono R L (Nat.sub_le_sub_right (Nat.add_le_add hl hm) 1)
        (symmetricAlgebraSymmetrize_prod_mul_sub_mem R L l m)
    | zero => simp
    | add Q T hQ hT ihQ ihT =>
      simpa only [mul_add, map_add, add_sub_add_comm] using
        (degreeFiltration R L (p + q - 1)).add_mem ihQ ihT
    | smul r Q hQ ih =>
      simpa only [mul_smul_comm, map_smul, smul_sub] using
        (degreeFiltration R L (p + q - 1)).smul_mem r ih
  | zero => simp
  | add P T hP hT ihP ihT =>
    simpa only [add_mul, map_add, add_sub_add_comm] using
      (degreeFiltration R L (p + q - 1)).add_mem ihP ihT
  | smul r P hP ih =>
    simpa only [smul_mul_assoc, map_smul, smul_sub] using
      (degreeFiltration R L (p + q - 1)).smul_mem r ih

end Langlands.Algebra.UniversalEnveloping
