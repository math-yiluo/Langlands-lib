import Langlands.HarmonicAnalysis.Distribution.Basic
import Langlands.Group.GL.Maps

/-! # Transpose transport on distributions on the actual general linear group -/

noncomputable section

namespace Langlands.HarmonicAnalysis.Distribution

universe uR uF

variable (n : ℕ) (R : Type uR) [CommRing R] [TopologicalSpace R]
variable [IsTopologicalRing R]

/-- Actual matrix transposition, constructed from inversion and inverse transpose. -/
def transposeHomeomorph :
    Matrix.GeneralLinearGroup (Fin n) R ≃ₜ Matrix.GeneralLinearGroup (Fin n) R :=
  (Homeomorph.inv _).trans (GeneralLinear.inverseTransposeContinuous n R).toHomeomorph

@[simp]
theorem transposeHomeomorph_apply (g : Matrix.GeneralLinearGroup (Fin n) R) :
    transposeHomeomorph n R g = GeneralLinear.inverseTranspose n R g⁻¹ := rfl

@[simp]
theorem transposeHomeomorph_coe (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (transposeHomeomorph n R g : Matrix (Fin n) (Fin n) R) = g.val.transpose := by
  simp only [transposeHomeomorph_apply, GeneralLinear.inverseTranspose_coe, inv_inv]

@[simp]
theorem transposeHomeomorph_entry (g : Matrix.GeneralLinearGroup (Fin n) R)
    (i j : Fin n) : transposeHomeomorph n R g i j = g j i := by
  simp only [transposeHomeomorph_apply, GeneralLinear.inverseTranspose_entry, inv_inv]

@[simp]
theorem transposeHomeomorph_involutive (g : Matrix.GeneralLinearGroup (Fin n) R) :
    transposeHomeomorph n R (transposeHomeomorph n R g) = g := by
  simp only [transposeHomeomorph_apply, ← map_inv, inv_inv,
    GeneralLinear.inverseTranspose_involutive]

/-- Transpose is an anti-automorphism on the group. -/
theorem transposeHomeomorph_mul (g h : Matrix.GeneralLinearGroup (Fin n) R) :
    transposeHomeomorph n R (g * h) =
      transposeHomeomorph n R h * transposeHomeomorph n R g := by
  simp only [transposeHomeomorph_apply, mul_inv_rev, map_mul]

/-- Transpose normalizes conjugation through the inverse-transpose automorphism. -/
theorem transposeHomeomorph_conjugation
    (a g : Matrix.GeneralLinearGroup (Fin n) R) :
    transposeHomeomorph n R (conjugationHomeomorph a g) =
      conjugationHomeomorph (GeneralLinear.inverseTranspose n R a)
        (transposeHomeomorph n R g) := by
  simp only [transposeHomeomorph_apply, conjugationHomeomorph_apply,
    mul_inv_rev, inv_inv, map_mul, map_inv, mul_assoc]

/-- Compatibility of the actual distribution pushforwards. -/
theorem pushforward_transpose_conjugation
    (a : Matrix.GeneralLinearGroup (Fin n) R)
    (D : Distribution (Matrix.GeneralLinearGroup (Fin n) R)) :
    pushforward (transposeHomeomorph n R) (pushforward (conjugationHomeomorph a) D) =
      pushforward (conjugationHomeomorph (GeneralLinear.inverseTranspose n R a))
        (pushforward (transposeHomeomorph n R) D) := by
  rw [← pushforward_trans, ← pushforward_trans]
  have he : (conjugationHomeomorph a).trans (transposeHomeomorph n R) =
      (transposeHomeomorph n R).trans
        (conjugationHomeomorph (GeneralLinear.inverseTranspose n R a)) := by
    apply Homeomorph.ext
    intro g
    exact transposeHomeomorph_conjugation n R a g
  rw [he]

@[simp]
theorem pushforward_transpose_involutive
    (D : Distribution (Matrix.GeneralLinearGroup (Fin n) R)) :
    pushforward (transposeHomeomorph n R)
      (pushforward (transposeHomeomorph n R) D) = D := by
  rw [← pushforward_trans]
  have he : (transposeHomeomorph n R).trans (transposeHomeomorph n R) =
      Homeomorph.refl _ := by
    apply Homeomorph.ext
    intro g
    exact transposeHomeomorph_involutive n R g
  rw [he, pushforward_refl]

/-- The proposition of invariance under actual matrix transposition. -/
def IsTransposeInvariant
    (D : Distribution (Matrix.GeneralLinearGroup (Fin n) R)) : Prop :=
  pushforward (transposeHomeomorph n R) D = D

theorem isTransposeInvariant_iff
    (D : Distribution (Matrix.GeneralLinearGroup (Fin n) R)) :
    IsTransposeInvariant n R D ↔
      ∀ f : SchwartzBruhat (Matrix.GeneralLinearGroup (Fin n) R),
        D (Hecke.TestFunction.pullback (transposeHomeomorph n R) f) = D f := by
  constructor
  · intro h f
    exact congrArg (fun E : Distribution (Matrix.GeneralLinearGroup (Fin n) R) => E f) h
  · intro h
    ext f
    exact h f

/-- Transposing a conjugation-invariant distribution preserves its conjugation
invariance; this does not say that the original distribution equals its transpose. -/
theorem IsConjugationInvariant.pushforward_transpose
    {D : Distribution (Matrix.GeneralLinearGroup (Fin n) R)}
    (hD : IsConjugationInvariant D) :
    IsConjugationInvariant (pushforward (transposeHomeomorph n R) D) := by
  intro a
  have h := pushforward_transpose_conjugation n R
    (GeneralLinear.inverseTranspose n R a) D
  rw [GeneralLinear.inverseTranspose_involutive, hD] at h
  exact h.symm

/-- The construction applies with the actual canonical topology of every p-adic field. -/
example {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (n : ℕ) :
    letI := F.canonicalNormedField
    GeneralLinear n F.Carrier ≃ₜ GeneralLinear n F.Carrier := by
  letI := F.canonicalNormedField
  exact transposeHomeomorph n F.Carrier

end Langlands.HarmonicAnalysis.Distribution
