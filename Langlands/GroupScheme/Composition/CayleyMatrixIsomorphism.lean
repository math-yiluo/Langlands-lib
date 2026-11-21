import Langlands.GroupScheme.Composition.CayleyCoefficientExtension
import Langlands.GroupScheme.Composition.CayleyGaloisTwist
import Langlands.GroupScheme.Composition.CayleyNormClassification

/-! # Matrices identifying two Cayley data -/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.CayleyDatum

open CayleyGaloisTwist

set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K] {c d e : CayleyDatum K}
variable {A B : Type u} [CommRing A] [CommRing B] (φ : K →+* A)

/-- An invertible matrix whose column-vector action identifies the units and
  multiplications of two Cayley data after extending coefficients. -/
def IsIsomorphismMatrix (c d : CayleyDatum K) (P : GL (Fin 8) A) : Prop :=
  (P : Matrix (Fin 8) (Fin 8) A) *ᵥ c.unitOver φ = d.unitOver φ ∧
    ∀ x y : CayleyVector A,
      (P : Matrix (Fin 8) (Fin 8) A) *ᵥ c.multiplicationOver φ x y =
        d.multiplicationOver φ ((P : Matrix (Fin 8) (Fin 8) A) *ᵥ x)
          ((P : Matrix (Fin 8) (Fin 8) A) *ᵥ y)

namespace IsIsomorphismMatrix

variable {φ} {P Q : GL (Fin 8) A}

/-- Composition of the corresponding maps is the usual product in column order. -/
theorem mul (hQ : IsIsomorphismMatrix φ d e Q) (hP : IsIsomorphismMatrix φ c d P) :
    IsIsomorphismMatrix φ c e (Q * P) := by
  refine ⟨?_, fun x y => ?_⟩
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hP.1, hQ.1]
  · simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
    rw [hP.2, hQ.2]

/-- The inverse carries the new unit and multiplication back to the original ones. -/
theorem inv (hP : IsIsomorphismMatrix φ c d P) : IsIsomorphismMatrix φ d c P⁻¹ := by
  refine ⟨mulVec_injective P ?_, fun x y => mulVec_injective P ?_⟩
  · rw [mulVec_inv_mulVec, hP.1]
  · rw [mulVec_inv_mulVec, hP.2, mulVec_inv_mulVec, mulVec_inv_mulVec]

/-- The multiplication condition can be checked on pairs of standard basis vectors. -/
theorem of_basis
    (hu : (P : Matrix (Fin 8) (Fin 8) A) *ᵥ c.unitOver φ = d.unitOver φ)
    (hm : ∀ i j : Fin 8,
      (P : Matrix (Fin 8) (Fin 8) A) *ᵥ c.multiplicationOver φ (Pi.single i 1) (Pi.single j 1) =
        d.multiplicationOver φ ((P : Matrix (Fin 8) (Fin 8) A) *ᵥ Pi.single i 1)
          ((P : Matrix (Fin 8) (Fin 8) A) *ᵥ Pi.single j 1)) : IsIsomorphismMatrix φ c d P := by
  let T := (P : Matrix (Fin 8) (Fin 8) A).mulVecLin
  let S := (c.multiplicationBilin φ).compr₂ T
  let S' := (d.multiplicationBilin φ).compl₁₂ T T
  have h : S = S' := by
    apply (Module.Basis.ext (Pi.basisFun A (Fin 8)))
    intro i
    apply (Module.Basis.ext (Pi.basisFun A (Fin 8)))
    intro j
    simpa only [S, S', T, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
      LinearMap.comp_apply, multiplicationBilin_apply, Matrix.mulVecLin_apply, Pi.basisFun_apply]
      using hm i j
  exact ⟨hu, fun x y => DFunLike.congr_fun (DFunLike.congr_fun h x) y⟩

private theorem map_vec_single (f : A →+* B) (i : Fin 8) :
    (fun j => f ((Pi.single i (1 : A) : CayleyVector A) j)) = Pi.single i 1 := by
  funext j
  by_cases h : j = i <;> simp [h]

/-- A scalar map takes an isomorphism matrix to an isomorphism matrix. -/
theorem map (hP : IsIsomorphismMatrix φ c d P) (f : A →+* B) :
    IsIsomorphismMatrix (f.comp φ) c d (GeneralLinearGroup.map f P) := by
  apply of_basis
  · have h := congrArg (fun v : CayleyVector A => fun i => f (v i)) hP.1
    rw [map_mulVec_fun, c.map_unitOver, d.map_unitOver] at h
    exact h
  · intro i j
    have h := congrArg (fun v : CayleyVector A => fun k => f (v k)) (hP.2 (Pi.single i 1) (Pi.single j 1))
    rw [map_mulVec_fun, c.map_multiplicationOver_vec, d.map_multiplicationOver_vec, map_mulVec_fun,
      map_mulVec_fun, map_vec_single, map_vec_single] at h
    exact h

/-- An injective scalar map reflects the unit and multiplication equations. -/
theorem of_map (f : A →+* B) (hf : Function.Injective f)
    (hP : IsIsomorphismMatrix (f.comp φ) c d (GeneralLinearGroup.map f P)) :
    IsIsomorphismMatrix φ c d P := by
  refine ⟨?_, fun x y => ?_⟩
  · have h := hP.1
    rw [coe_map, ← c.map_unitOver, ← d.map_unitOver, ← map_mulVec_fun] at h
    exact funext fun i => hf (congrFun h i)
  · have h := hP.2 (fun i => f (x i)) (fun i => f (y i))
    rw [coe_map, ← c.map_multiplicationOver_vec, ← map_mulVec_fun, ← map_mulVec_fun,
      ← map_mulVec_fun, ← d.map_multiplicationOver_vec] at h
    exact funext fun i => hf (congrFun h i)

/-- An algebra isomorphism matrix induces an isometry of the extended norms. -/
def normIsometry [Infinite K] [Invertible (2 : K)] {L : Type u} [Field L]
    {ψ : K →+* L} {P : GL (Fin 8) L} (hP : IsIsomorphismMatrix ψ c d P) :
    (c.normOver ψ).IsometryEquiv (d.normOver ψ) := by
  let E := (GeneralLinearGroup.toLin P).toLinearEquiv
  refine ⟨E, fun x => ?_⟩
  exact (c.extend ψ).norm_eq_of_preserves_mul_unit (d.extend ψ) E hP.1 hP.2 x

end IsIsomorphismMatrix

/-- A linear equivalence preserving the unit and product gives an isomorphism matrix. -/
theorem exists_isIsomorphismMatrix_of_linearEquiv (l : CayleyVector K ≃ₗ[K] CayleyVector K)
    (hu : l c.unit = d.unit)
    (hm : ∀ x y, l (c.multiplication x y) = d.multiplication (l x) (l y)) :
    ∃ P, IsIsomorphismMatrix (RingHom.id K) c d P := by
  let P := GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv l)
  have hP (x : CayleyVector K) : (P : Matrix (Fin 8) (Fin 8) K) *ᵥ x = l x := by
    have h := GeneralLinearGroup.toLin_apply P x
    rw [show GeneralLinearGroup.toLin P = LinearMap.GeneralLinearGroup.ofLinearEquiv l from
      MulEquiv.apply_symm_apply _ _] at h
    exact h.symm
  refine ⟨P, ?_, fun x y => ?_⟩
  · rw [unitOver_self, unitOver_self, hP, hu]
  · rw [multiplicationOver_self, hP, hP, hP, multiplicationOver_self, hm]

end Langlands.GroupScheme.CayleyDatum
