import Langlands.Algebra.GroupAlgebraCoaction
import Langlands.Algebra.NilpotentModuleReduction

/-! # Nilpotent rigidity of central group-algebra coactions -/

noncomputable section

universe u v w

open TensorProduct Coalgebra

namespace Langlands.GroupAlgebraCoaction

section Coalgebra

variable {K : Type u} [CommRing K] {A : Type v} [AddCommGroup A] [Module K A]
  [Coalgebra K A]

theorem apply_lact (f g : A →ₗ[K] K) (a : A) :
    f (lact g a) = conv g f a := by
  let 𝓡 := Repr.arbitrary K a
  rw [lact_apply 𝓡, conv_apply 𝓡, map_sum]
  simp only [map_smul, smul_eq_mul]

theorem lact_lact (f g : A →ₗ[K] K) (a : A) :
    lact f (lact g a) = lact (conv g f) a := by
  let 𝓡 := Repr.arbitrary K a
  calc
    lact f (lact g a) =
        TensorProduct.lid K A (f.rTensor A ((lact g).rTensor A (comul a))) := by
      rw [rTensor_lact_comul]
      rfl
    _ = ∑ i ∈ 𝓡.index, f (lact g (𝓡.left i)) • 𝓡.right i := by
      rw [← 𝓡.eq]
      simp
    _ = lact (conv g f) a := by
      simp only [apply_lact]
      exact (lact_apply 𝓡 _).symm

theorem ract_lact (f g : A →ₗ[K] K) (a : A) :
    ract f (lact g a) = lact g (ract f a) := by
  change TensorProduct.rid K A (f.lTensor A (comul (lact g a))) =
    lact g (TensorProduct.rid K A (f.lTensor A (comul a)))
  rw [← rTensor_lact_comul]
  generalize comul (R := K) a = t
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

theorem ract_commute_lact (f g : A →ₗ[K] K) : Commute (ract f) (lact g) := by
  ext a
  exact ract_lact f g a

end Coalgebra

section Bialgebra

variable {K : Type u} [CommRing K] {N : Type w} [AddCommGroup N]
variable {A : Type v} [CommRing A] [Bialgebra K A] (π : A →ₐc[K] AddMonoidAlgebra K N)

/-- The left coaction, with its tensor factors reordered to `A ⊗ K[N]`. -/
def leftCoaction : A →ₐ[K] AddMonoidAlgebra A N :=
  ((AddMonoidAlgebra.scalarTensorEquiv K A (M := N)).toAlgHom.restrictScalars K).comp
    ((Algebra.TensorProduct.comm K (AddMonoidAlgebra K N) A).toAlgHom.comp
      ((Algebra.TensorProduct.map (π : A →ₐ[K] AddMonoidAlgebra K N)
        (AlgHom.id K A)).comp (Bialgebra.comulAlgHom K A)))

theorem leftCoaction_apply (a : A) :
    leftCoaction π a = AddMonoidAlgebra.scalarTensorEquiv K A
      (TensorProduct.comm K _ A
        ((π : A →ₗ[K] AddMonoidAlgebra K N).rTensor A (comul a))) := rfl

theorem coeff_leftCoaction (a : A) (n : N) :
    (leftCoaction π a).coeff n = lact (coeffForm π n) a := by
  let 𝓡 := Repr.arbitrary K a
  rw [leftCoaction_apply, ← 𝓡.eq, lact_apply 𝓡]
  simp [coeffForm, Algebra.smul_def, Algebra.commutes]

open Classical in
theorem lact_coeffForm_lact_coeffForm (m n : N) (a : A) :
    lact (coeffForm π m) (lact (coeffForm π n) a) =
      if m = n then lact (coeffForm π n) a else 0 := by
  classical
  rcases eq_or_ne m n with rfl | h
  · rw [lact_lact, conv_coeffForm]
    simp
  · rw [lact_lact, conv_coeffForm]
    simp [h, Ne.symm h, lact]

theorem isIdempotentElem_lact_coeffForm (n : N) :
    IsIdempotentElem (lact (coeffForm π n)) := by
  ext a
  simpa using lact_coeffForm_lact_coeffForm π n n a

theorem isIdempotentElem_proj (n : N) : IsIdempotentElem (proj π n) := by
  ext a
  simpa using proj_proj π n n a

theorem isCentral_iff_leftCoaction_eq_coaction :
    IsCentral π ↔ leftCoaction π = coaction π := by
  constructor
  · intro h
    ext a n
    rw [coeff_leftCoaction, coeff_coaction]
    exact h.lact_coeffForm n a
  · intro h a
    have ha := AlgHom.congr_fun h a
    rw [leftCoaction_apply, coaction_apply] at ha
    have hb := (AddMonoidAlgebra.scalarTensorEquiv K A).injective ha
    apply (TensorProduct.comm K _ A).injective
    simpa using hb

theorem isCentral_iff_lact_coeffForm_eq_proj :
    IsCentral π ↔ ∀ n : N, lact (coeffForm π n) = proj π n := by
  constructor
  · intro h n
    ext a
    exact h.lact_coeffForm n a
  · intro h
    apply (isCentral_iff_leftCoaction_eq_coaction π).mpr
    ext a n
    rw [coeff_leftCoaction, coeff_coaction, h]

/-- Character projections congruent modulo a nilpotent base ideal agree exactly. -/
theorem isCentral_of_coeff_sub_mem (I : Ideal K) (hI : IsNilpotent I)
    (h : ∀ (n : N) (a : A),
      lact (coeffForm π n) a - proj π n a ∈ I • (⊤ : Submodule K A)) :
    IsCentral π := by
  apply (isCentral_iff_lact_coeffForm_eq_proj π).mpr
  intro n
  apply Langlands.NilpotentModuleReduction.eq_of_sub_mem I hI
    (isIdempotentElem_lact_coeffForm π n) (isIdempotentElem_proj π n)
    (ract_commute_lact (coeffForm π n) (coeffForm π n)).symm
  exact h n

end Bialgebra

end Langlands.GroupAlgebraCoaction
