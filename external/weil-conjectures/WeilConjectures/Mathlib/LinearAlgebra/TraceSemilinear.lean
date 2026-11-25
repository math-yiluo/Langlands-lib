/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Trace

/-!
# Traces along semilinear equivalences

Let `ρ : K ≃+* R` be an isomorphism of commutative rings, `V` a finite free `K`-module, `W` an
`R`-module and `e : V ≃+ W` an additive equivalence which is `ρ`-semilinear,
`e (c • v) = ρ c • e v`. If `e` intertwines a `K`-linear endomorphism `f` of `V` with an
`R`-linear endomorphism `g` of `W`, then `tr g = ρ (tr f)`
(`LinearMap.trace_eq_ringEquiv_trace_of_addEquiv`).
-/

@[expose] public section

namespace LinearMap

variable {K R V W : Type*} [CommRing K] [CommRing R] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module R W]

/-- **The trace along a semilinear equivalence**: if a `ρ`-semilinear additive equivalence
`e : V ≃+ W`, for a ring isomorphism `ρ : K ≃+* R` and `V` finite free over `K`, intertwines
endomorphisms `f` and `g`, then `tr g = ρ (tr f)`. -/
theorem trace_eq_ringEquiv_trace_of_addEquiv [Module.Free K V] [Module.Finite K V]
    (ρ : K ≃+* R) (e : V ≃+ W) (he : ∀ (c : K) (v : V), e (c • v) = ρ c • e v)
    (f : V →ₗ[K] V) (g : W →ₗ[R] W) (h : ∀ v, e (f v) = g (e v)) :
    trace R W g = ρ (trace K V f) := by
  classical
  let ι := Module.Free.ChooseBasisIndex K V
  let b : Module.Basis ι K V := Module.Free.chooseBasis K V
  have hs (r : R) (w : W) : e.symm (r • w) = ρ.symm r • e.symm w := by
    apply e.injective
    rw [AddEquiv.apply_symm_apply, he, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  let eW : W ≃ₗ[R] (ι → R) :=
    { toFun w i := ρ (b.equivFun (e.symm w) i)
      invFun x := e (b.equivFun.symm fun i ↦ ρ.symm (x i))
      map_add' w w' := funext fun i ↦ by simp
      map_smul' r w := funext fun i ↦ by simp [hs]
      left_inv w := by simp
      right_inv x := funext fun i ↦ by
        simp only [AddEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply,
          RingEquiv.apply_symm_apply] }
  let b' : Module.Basis ι R W := Module.Basis.ofEquivFun eW
  have hb' (i : ι) : b' i = e (b i) := by
    rw [Module.Basis.coe_ofEquivFun]
    change e (b.equivFun.symm fun j ↦ ρ.symm ((Pi.single i (1 : R) : ι → R) j)) = e (b i)
    congr 1
    refine b.equivFun.injective (funext fun j ↦ ?_)
    rw [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_self, Pi.single_apply]
    split_ifs with h₁ h₂ h₂
    · exact map_one _
    · exact absurd h₁.symm h₂
    · exact absurd h₂.symm h₁
    · exact map_zero _
  have hrepr (w : W) (i : ι) : b'.repr w i = ρ (b.repr (e.symm w) i) := by
    rw [Module.Basis.ofEquivFun_repr_apply]
    rfl
  rw [trace_eq_matrix_trace R b', trace_eq_matrix_trace K b, Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, toMatrix_apply, toMatrix_apply, hb', ← h, hrepr,
    AddEquiv.symm_apply_apply]

end LinearMap
