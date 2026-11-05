import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Descent detected by an embedding of field algebras -/

noncomputable section

universe u v w x y

open scoped TensorProduct

namespace Langlands.TensorEmbeddingDescent

variable {k : Type u} [Field k]
    {K : Type v} [CommRing K] [Algebra k K]
    {A : Type w} [CommRing A] [Algebra k A]
    {B : Type x} [CommRing B] [Algebra k B]

/-- If a tensor becomes a ground-field element after an injective algebra map,
then it was already a ground-field element. -/
theorem exists_includeRight_eq_of_map_eq
    (f : A →ₐ[k] B) (hf : Function.Injective f)
    (z : K ⊗[k] A) (b : B)
    (hz : Algebra.TensorProduct.map (AlgHom.id k K) f z =
      (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) b) :
    ∃ a : A, (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) a = z := by
  obtain ⟨r, hr⟩ := f.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hf)
  refine ⟨r b, ?_⟩
  have h := congrArg (r.lTensor K) hz
  change (r.lTensor K) ((f.toLinearMap.lTensor K) z) =
    (1 : K) ⊗ₜ[k] r b at h
  rw [← LinearMap.lTensor_comp_apply, hr, LinearMap.lTensor_id_apply] at h
  exact h.symm

/-- Scalar extension reflects whether the image of a tensor comes from the base algebra. -/
theorem map_mem_range_includeRight_iff
    (f : A →ₐ[k] B) (hf : Function.Injective f) (z : K ⊗[k] A) :
    Algebra.TensorProduct.map (AlgHom.id k K) f z ∈
        (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).range ↔
      z ∈ (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).range := by
  constructor
  · rintro ⟨b, hb⟩
    exact exists_includeRight_eq_of_map_eq f hf z b hb.symm
  · rintro ⟨a, rfl⟩
    exact ⟨f a, rfl⟩

variable [Nontrivial K] {C : Type y} [CommRing C] [Algebra k C]

/-- An algebra map descends whenever its composite with an embedding descends.
There are no algebraicity or separability hypotheses on the coefficient extension. -/
theorem existsUnique_algHom_of_map_eq
    (f : A →ₐ[k] B) (hf : Function.Injective f)
    (g : C →ₐ[k] K ⊗[k] A) (h : C →ₐ[k] B)
    (hgh : (Algebra.TensorProduct.map (AlgHom.id k K) f).comp g =
      (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).comp h) :
    ∃! g₀ : C →ₐ[k] A,
      (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).comp g₀ = g := by
  let j : A →ₐ[k] K ⊗[k] A := Algebra.TensorProduct.includeRight
  have hj : Function.Injective j :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
  have hg : ∀ c, g c ∈ j.range := fun c =>
    exists_includeRight_eq_of_map_eq f hf (g c) (h c) (DFunLike.congr_fun hgh c)
  let g₀ : C →ₐ[k] A :=
    (AlgEquiv.ofInjective j hj).symm.toAlgHom.comp (g.codRestrict j.range hg)
  have hg₀ : j.comp g₀ = g := by
    ext c
    change ((AlgEquiv.ofInjective j hj)
      ((AlgEquiv.ofInjective j hj).symm ⟨g c, hg c⟩)).val = g c
    rw [AlgEquiv.apply_symm_apply]
  refine ⟨g₀, hg₀, ?_⟩
  intro g₁ hg₁
  apply AlgHom.ext
  intro c
  apply hj
  exact (DFunLike.congr_fun hg₁ c).trans (DFunLike.congr_fun hg₀ c).symm

/-- The algebra map descended through the given embedding. -/
def descendAlgHom
    (f : A →ₐ[k] B) (hf : Function.Injective f)
    (g : C →ₐ[k] K ⊗[k] A) (h : C →ₐ[k] B)
    (hgh : (Algebra.TensorProduct.map (AlgHom.id k K) f).comp g =
      (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).comp h) :
    C →ₐ[k] A :=
  (existsUnique_algHom_of_map_eq f hf g h hgh).choose

/-- Extending coefficients recovers the original algebra map. -/
theorem includeRight_comp_descendAlgHom
    (f : A →ₐ[k] B) (hf : Function.Injective f)
    (g : C →ₐ[k] K ⊗[k] A) (h : C →ₐ[k] B)
    (hgh : (Algebra.TensorProduct.map (AlgHom.id k K) f).comp g =
      (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).comp h) :
    (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).comp
      (descendAlgHom f hf g h hgh) = g :=
  (existsUnique_algHom_of_map_eq f hf g h hgh).choose_spec.1

end Langlands.TensorEmbeddingDescent
