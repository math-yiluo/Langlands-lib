import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Finite evaluation matrices for a family of linear maps to functions -/

noncomputable section

namespace Langlands.Global.EisensteinJet

open Module

variable {𝕜 V X : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- An injective map from a finite-dimensional space to scalar functions has
an evaluation isomorphism at a list of points of length the dimension. -/
theorem exists_evaluationEquiv (f : V →ₗ[𝕜] (X → 𝕜)) (hf : Function.Injective f) :
    ∃ (p : Fin (finrank 𝕜 V) → X) (e : V ≃ₗ[𝕜] (Fin (finrank 𝕜 V) → 𝕜)),
      ∀ v i, e v i = f v (p i) := by
  classical
  let L (x : X) : Dual 𝕜 V := (LinearMap.proj x).comp f
  have hspan : Submodule.span 𝕜 (Set.range L) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro v hv
    have hv' : f v ≠ 0 := fun h => hv (hf (h.trans (map_zero f).symm))
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hv'
    exact ⟨L x, ⟨x, rfl⟩, hx⟩
  have hrank : finrank 𝕜 (Submodule.span 𝕜 (Set.range L)) = finrank 𝕜 V := by
    rw [hspan, finrank_top, Subspace.dual_finrank_eq]
  have hg := Submodule.exists_fun_fin_finrank_span_eq 𝕜 (Set.range L)
  rw [hrank] at hg
  obtain ⟨g, hg, hspan_g, _⟩ := hg
  choose p hp using hg
  let M := (LinearMap.funLeft 𝕜 𝕜 p).comp f
  have hM : Function.Injective M := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (by
    intro v hv
    have hker : Submodule.span 𝕜 (Set.range g) ≤ LinearMap.ker (Dual.eval 𝕜 V v) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      rw [← hp i]
      exact LinearMap.mem_ker.mpr (congrFun hv i)
    apply (Module.eval_apply_eq_zero_iff 𝕜 v).mp
    exact LinearMap.ker_eq_top.mp (top_unique (hspan_g.trans hspan ▸ hker))))
  have hsurj : Function.Surjective M :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Module.finrank_fin_fun (R := 𝕜)).symm).mp hM
  exact ⟨p, LinearEquiv.ofBijective M ⟨hM, hsurj⟩, fun _ _ => rfl⟩

/-- Coordinates in the source and point evaluations in the target make a
square matrix for the linear map. -/
def evaluationMatrix (p : Fin (finrank 𝕜 V) → X)
    (e : V ≃ₗ[𝕜] (Fin (finrank 𝕜 V) → 𝕜)) (f : V →ₗ[𝕜] (X → 𝕜)) :
    Matrix (Fin (finrank 𝕜 V)) (Fin (finrank 𝕜 V)) 𝕜 :=
  Matrix.of fun i j => f (e.symm (Pi.single j 1)) (p i)

/-- A choice of evaluations and source coordinates makes the matrix of an
injective member of the family the identity. -/
theorem exists_evaluationMatrix_eq_one (f : V →ₗ[𝕜] (X → 𝕜))
    (hf : Function.Injective f) :
    ∃ (p : Fin (finrank 𝕜 V) → X) (e : V ≃ₗ[𝕜] (Fin (finrank 𝕜 V) → 𝕜)),
      evaluationMatrix p e f = 1 := by
  obtain ⟨p, e, he⟩ := exists_evaluationEquiv f hf
  refine ⟨p, e, ?_⟩
  ext i j
  change f (e.symm (Pi.single j 1)) (p i) = _
  rw [← he, e.apply_symm_apply, Matrix.one_apply, Pi.single_apply, eq_comm]

end Langlands.Global.EisensteinJet
