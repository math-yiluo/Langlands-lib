import Langlands.Global.EisensteinEvaluationMatrix
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.DFinsupp

/-! # Finite evaluation with values in prescribed function subspaces -/

noncomputable section

universe u v

open scoped BigOperators

set_option autoImplicit false

namespace Langlands.Analysis

/-- A function in the finite sum of finite-dimensional spaces can be
reconstructed from finitely many point evaluations, with each part of
the reconstruction lying in its prescribed subspace. -/
def FiniteSubspaceInterpolationStatement : Prop :=
  ∀ (X : Type u) (A : Type v) [Fintype A] (W : A → Submodule ℂ (X → ℂ))
    [∀ i, FiniteDimensional ℂ (W i)],
    ∃ (m : ℕ) (nodes : Fin m → X) (weights : A → Fin m → X → ℂ),
      (∀ i j, weights i j ∈ W i) ∧
      ∀ f : X → ℂ, f ∈ ⨆ i, W i →
        ∀ x, f x = ∑ i, ∑ j, weights i j x * f (nodes j)

theorem finiteSubspaceInterpolation : FiniteSubspaceInterpolationStatement.{u,v} := by
  intro X A _ W _
  classical
  let V := ⨆ i, W i
  let sumMap : ((i : A) → W i) →ₗ[ℂ] V :=
    { toFun := fun f => ⟨∑ i, (f i : X → ℂ), V.sum_mem fun i _ => le_iSup W i (f i).property⟩
      map_add' := fun f g => by
        apply Subtype.ext
        simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
      map_smul' := fun c f => by
        apply Subtype.ext
        simp only [Pi.smul_apply, Submodule.coe_smul, Finset.smul_sum, RingHom.id_apply] }
  have hSurj : Function.Surjective sumMap := by
    intro f
    have hf : (f : X → ℂ) ∈ ⨆ i ∈ (Finset.univ : Finset A), W i := by
      simp only [Finset.mem_univ, iSup_pos]
      exact f.property
    obtain ⟨g, hg⟩ := (Submodule.mem_iSup_finset_iff_exists_sum W (f : X → ℂ)).mp hf
    exact ⟨g, Subtype.ext hg⟩
  obtain ⟨sec, hsec⟩ := sumMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hSurj)
  obtain ⟨nodes, e, he⟩ := Langlands.Global.EisensteinJet.exists_evaluationEquiv V.subtype
    (Submodule.injective_subtype V)
  let extract := sec.comp e.symm.toLinearMap
  let weights (i : A) (j : Fin (Module.finrank ℂ V)) := (extract (Pi.single j 1) i : X → ℂ)
  refine ⟨_, nodes, weights, fun i j => (extract (Pi.single j 1) i).property, ?_⟩
  intro f hf x
  let v : V := ⟨f, hf⟩
  have hInput : (∑ j, e v j • (Pi.single j 1 : Fin (Module.finrank ℂ V) → ℂ)) = e v := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hExtract : extract (e v) = ∑ j, e v j • extract (Pi.single j 1) := by
    calc
      extract (e v) = extract (∑ j, e v j • Pi.single j 1) := congrArg extract hInput.symm
      _ = _ := by simp only [map_sum, map_smul]
  have hSum : sumMap (extract (e v)) = v := by
    change sumMap (sec (e.symm (e v))) = v
    rw [LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun hsec v
  calc
    f x = ∑ i, (extract (e v) i : X → ℂ) x := by
      simpa only [sumMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, v] using
        (congrFun (congrArg Subtype.val hSum) x).symm
    _ = _ := by
      rw [hExtract]
      simp only [Finset.sum_apply, Pi.smul_apply, Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul, he,
        Submodule.subtype_apply, v, weights]
      simp only [mul_comm]

end Langlands.Analysis
