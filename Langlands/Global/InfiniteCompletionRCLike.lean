import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Analysis.Complex.Basic

/-! # Compatible real or complex structure on the actual infinite completion -/

noncomputable section

universe u v

open scoped ComplexOrder

namespace Langlands.Analytic

variable {K : Type u} {k : Type v} [NormedField K] [CompleteSpace K] [RCLike k]

/-- Pull the real or complex analytic structure back along a norm-preserving
ring equivalence, retaining the given normed field structure on the source. -/
@[instance_reducible]
def rclikeOfNormPreservingRingEquiv (e : K ≃+* k)
    (hn : ∀ x, ‖e x‖ = ‖x‖) : RCLike K := by
  letI : Algebra ℝ K :=
    (e.symm.toRingHom.comp (algebraMap ℝ k)).toAlgebra
  letI : StarRing K := {
    star := fun x => e.symm (star (e x))
    star_involutive := by
      intro x
      simp
    star_mul := by
      intro x y
      simp [map_mul, mul_comm]
    star_add := by
      intro x y
      simp [map_add]
  }
  letI : NormedAlgebra ℝ K := {
    norm_smul_le := by
      intro r x
      change ‖e.symm ((algebraMap ℝ k) r) * x‖ ≤ ‖r‖ * ‖x‖
      rw [← hn, map_mul, e.apply_symm_apply, ← Algebra.smul_def, norm_smul, hn]
  }
  exact {
    __ := ‹NormedField K›
    __ := ‹CompleteSpace K›
    __ := ‹StarRing K›
    __ := ‹NormedAlgebra ℝ K›
    lt_norm_lt := by
      intro x y hx hxy
      obtain ⟨a, ha, hb⟩ :=
        DenselyNormedField.lt_norm_lt (α := k) x y hx hxy
      refine ⟨e.symm a, ?_⟩
      have hna : ‖e.symm a‖ = ‖a‖ := by
        simpa only [e.apply_symm_apply] using (hn (e.symm a)).symm
      simpa only [hna] using And.intro ha hb
    re := RCLike.re.comp e.toAddMonoidHom
    im := RCLike.im.comp e.toAddMonoidHom
    I := e.symm RCLike.I
    I_re_ax := by
      simp
    I_mul_I_ax := by
      rcases RCLike.I_mul_I (K := k) with h | h
      · left
        exact map_eq_zero_iff _ e.symm.injective |>.mpr h
      · right
        apply e.injective
        simpa only [map_mul, e.apply_symm_apply, map_neg, map_one] using h
    re_add_im_ax := by
      intro x
      apply e.injective
      change e (e.symm ((RCLike.re (e x) : k)) +
        e.symm ((RCLike.im (e x) : k)) * e.symm RCLike.I) = e x
      simpa only [map_add, map_mul, e.apply_symm_apply] using
        RCLike.re_add_im (e x)
    ofReal_re_ax := by
      intro r
      change RCLike.re (e (e.symm ((r : k)))) = r
      simp
    ofReal_im_ax := by
      intro r
      change RCLike.im (e (e.symm ((r : k)))) = 0
      simp
    mul_re_ax := by
      intro x y
      change RCLike.re (e (x * y)) =
        RCLike.re (e x) * RCLike.re (e y) -
          RCLike.im (e x) * RCLike.im (e y)
      rw [map_mul, RCLike.mul_re]
    mul_im_ax := by
      intro x y
      change RCLike.im (e (x * y)) =
        RCLike.re (e x) * RCLike.im (e y) +
          RCLike.im (e x) * RCLike.re (e y)
      rw [map_mul, RCLike.mul_im]
    conj_re_ax := by
      intro x
      change RCLike.re (e (e.symm (star (e x)))) = RCLike.re (e x)
      simp
    conj_im_ax := by
      intro x
      change RCLike.im (e (e.symm (star (e x)))) = -RCLike.im (e x)
      simp
    conj_I_ax := by
      change e.symm (star (e (e.symm RCLike.I))) = -e.symm RCLike.I
      simp
    norm_sq_eq_def_ax := by
      intro x
      change ‖x‖ ^ 2 =
        RCLike.re (e x) * RCLike.re (e x) +
          RCLike.im (e x) * RCLike.im (e x)
      simpa only [hn] using (RCLike.norm_sq_eq_def (z := e x))
    mul_im_I_ax := by
      intro x
      change RCLike.im (e x) * RCLike.im (e (e.symm RCLike.I)) =
        RCLike.im (e x)
      simpa only [e.apply_symm_apply] using RCLike.mul_im_I_ax (e x)
    toPartialOrder := PartialOrder.lift e e.injective
    le_iff_re_im := by
      intro x y
      exact RCLike.le_iff_re_im
    toDecidableEq := Classical.decEq K
  }

/-- Existence of a compatible analytic structure follows from an actual
norm-preserving ring equivalence, even across universes. -/
theorem isRCLikeNormedField_of_ringEquiv (e : K ≃+* k)
    (hn : ∀ x, ‖e x‖ = ‖x‖) : IsRCLikeNormedField K :=
  ⟨⟨rclikeOfNormPreservingRingEquiv e hn, rfl⟩⟩

end Langlands.Analytic

namespace NumberField.InfinitePlace

variable {F : Type u} [Field F]

/-- The actual infinite completion has a compatible real or complex
structure; its existing field, norm and topology are retained. -/
theorem completion_isRCLikeNormedField (v : InfinitePlace F) :
    IsRCLikeNormedField v.Completion := by
  rcases v.isReal_or_isComplex with hv | hv
  · apply Langlands.Analytic.isRCLikeNormedField_of_ringEquiv
      (Completion.ringEquivRealOfIsReal hv)
    intro x
    exact (AddMonoidHomClass.isometry_iff_norm _).mp
      (Completion.isometry_extensionEmbeddingOfIsReal hv) x
  · apply Langlands.Analytic.isRCLikeNormedField_of_ringEquiv
      (Completion.ringEquivComplexOfIsComplex hv)
    intro x
    exact (AddMonoidHomClass.isometry_iff_norm _).mp
      (Completion.isometry_extensionEmbedding v) x

end NumberField.InfinitePlace
