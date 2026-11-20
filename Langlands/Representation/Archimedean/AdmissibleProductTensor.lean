import Langlands.Representation.KFiniteDual
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Finite-dimensional coordinate spans and algebraic multiplicity tensors -/

noncomputable section

universe uV uW uI uK

open scoped Matrix TensorProduct

set_option autoImplicit false

namespace Langlands.Archimedean

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {I : Type uI}

/-- A tensor with a space of scalar families evaluates in the product of copies of `V`. -/
abbrev evalMultiplicityTensor :
    V ⊗[ℂ] (I → ℂ) →ₗ[ℂ] (I → V) :=
  TensorProduct.piScalarRightHom ℂ ℂ V I

theorem evalMultiplicityTensor_injective :
    Function.Injective (evalMultiplicityTensor (V := V) (I := I)) := by
  classical
  let b := Module.Free.chooseBasis ℂ V
  have h (x : V ⊗[ℂ] (I → ℂ)) (j : Module.Free.ChooseBasisIndex ℂ V) (i : I) :
      TensorProduct.equivFinsuppOfBasisLeft b x j i =
        b.coord j (evalMultiplicityTensor x i) := by
    induction x using TensorProduct.inductionOn with
    | tmul v c =>
      simp only [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Pi.smul_apply,
        evalMultiplicityTensor, TensorProduct.piScalarRightHom_tmul, map_smul,
        Module.Basis.coord_apply, smul_eq_mul]
      exact mul_comm _ _
    | add x y hx hy =>
      simp only [map_add, Finsupp.add_apply, Pi.add_apply, hx, hy]
  intro x y hxy
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  apply Finsupp.ext
  intro j
  funext i
  rw [h, h, hxy]

/-- A family with finite-dimensional span of its values has an algebraic tensor preimage. -/
theorem mem_range_evalMultiplicityTensor_of_finite (f : I → V)
    [FiniteDimensional ℂ (Submodule.span ℂ (Set.range f))] :
    f ∈ (evalMultiplicityTensor (V := V) (I := I)).range := by
  let S := Submodule.span ℂ (Set.range f)
  let b := Module.finBasis ℂ S
  have hf (i : I) : f i ∈ S := Submodule.subset_span ⟨i, rfl⟩
  refine ⟨∑ j, (b j : V) ⊗ₜ[ℂ] (fun i => b.repr ⟨f i, hf i⟩ j), ?_⟩
  funext i
  simpa only [map_sum, Finset.sum_apply, evalMultiplicityTensor,
    TensorProduct.piScalarRightHom_tmul, Submodule.coe_sum, Submodule.coe_smul]
    using congrArg Subtype.val (b.sum_repr ⟨f i, hf i⟩)

/-- Evaluation is compatible with operating on the vector factor alone. -/
theorem evalMultiplicityTensor_map (D : Module.End ℂ V)
    (x : V ⊗[ℂ] (I → ℂ)) (i : I) :
    evalMultiplicityTensor (TensorProduct.map D (LinearMap.id : Module.End ℂ (I → ℂ)) x) i =
      D (evalMultiplicityTensor x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul v c =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, evalMultiplicityTensor,
      TensorProduct.piScalarRightHom_tmul, map_smul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Lift a linear family of coordinates to algebraic tensors when each coordinate family
has finite-dimensional span of its values. -/
def toMultiplicityTensor (e : W →ₗ[ℂ] (I → V))
    (he : ∀ w, FiniteDimensional ℂ (Submodule.span ℂ (Set.range (e w)))) :
    W →ₗ[ℂ] V ⊗[ℂ] (I → ℂ) :=
  (LinearEquiv.ofInjective _ evalMultiplicityTensor_injective).symm.toLinearMap.comp
    (e.codRestrict _ fun w => by
      let := he w
      exact mem_range_evalMultiplicityTensor_of_finite (e w))

@[simp]
theorem evalMultiplicityTensor_toMultiplicityTensor (e : W →ₗ[ℂ] (I → V))
    (he : ∀ w, FiniteDimensional ℂ (Submodule.span ℂ (Set.range (e w))))
    (w : W) :
    evalMultiplicityTensor (toMultiplicityTensor e he w) = e w := by
  exact congrArg Subtype.val
    ((LinearEquiv.ofInjective _ evalMultiplicityTensor_injective).apply_symm_apply
      (e.codRestrict _ (fun w => by
        let := he w
        exact mem_range_evalMultiplicityTensor_of_finite (e w)) w))

theorem toMultiplicityTensor_injective (e : W →ₗ[ℂ] (I → V))
    (he : ∀ w, FiniteDimensional ℂ (Submodule.span ℂ (Set.range (e w))))
    (hinj : Function.Injective e) : Function.Injective (toMultiplicityTensor e he) := by
  intro w w' h
  apply hinj
  simpa only [evalMultiplicityTensor_toMultiplicityTensor] using congrArg evalMultiplicityTensor h

/-- The tensor lift preserves any simultaneous linear equivariance of the coordinates. -/
theorem toMultiplicityTensor_equivariant (e : W →ₗ[ℂ] (I → V))
    (he : ∀ w, FiniteDimensional ℂ (Submodule.span ℂ (Set.range (e w))))
    (D : Module.End ℂ W) (d : Module.End ℂ V)
    (hD : ∀ w i, e (D w) i = d (e w i)) (w : W) :
    toMultiplicityTensor e he (D w) =
      TensorProduct.map d (LinearMap.id : Module.End ℂ (I → ℂ)) (toMultiplicityTensor e he w) := by
  apply evalMultiplicityTensor_injective
  funext i
  rw [evalMultiplicityTensor_map, evalMultiplicityTensor_toMultiplicityTensor,
    evalMultiplicityTensor_toMultiplicityTensor]
  exact hD w i

variable {K : Type uK} [Group K] [TopologicalSpace K]

/-- All coordinates of a vector in one continuous finite-dimensional compact type
lie in a finite-dimensional space in an admissible target. -/
theorem finiteDimensional_span_range_intertwiners (ρ : Representation ℂ K V)
    (hρ : IsAdmissibleGKModule ρ) (d : ℕ) (τ : K →* Matrix (Fin d) (Fin d) ℂ)
    (hτ : Continuous τ) (q : I → gkIntertwiners ρ d τ) (w : Fin d → ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun i => (q i).val w)) := by
  let := hρ d τ hτ
  let ev : gkIntertwiners ρ d τ →ₗ[ℂ] V :=
    { toFun T := T.val w
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  apply Submodule.finiteDimensional_of_le (S₂ := ev.range)
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨q i, rfl⟩

/-- The coordinates of a compact-finite source vector in copies of an admissible
target have a common finite-dimensional span. -/
theorem finiteDimensional_span_range_of_compactCoordinates
    (κ : Representation ℂ K W) (ρ : Representation ℂ K V) (hρ : IsAdmissibleGKModule ρ)
    (hκ : ∀ (w : W) (ℓ : W →ₗ[ℂ] ℂ), Continuous fun k => ℓ (κ k w))
    (e : W →ₗ[ℂ] (I → V)) (he : ∀ k w i, e (κ k w) i = ρ k (e w i))
    (w : W) (hw : FiniteVectors.IsFiniteVector κ w) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range (e w))) := by
  let S := FiniteVectors.orbitSubrepresentation κ w
  let _ : FiniteDimensional ℂ S.toSubmodule := hw
  let b := Module.finBasis ℂ S.toSubmodule
  let d := Module.finrank ℂ S.toSubmodule
  let τ := KFiniteDual.subMatrix S
  let q (i : I) : gkIntertwiners ρ d τ :=
    ⟨(LinearMap.proj i).comp (e.comp (S.toSubmodule.subtype.comp b.equivFun.symm.toLinearMap)), by
      intro k x
      change e (b.equivFun.symm (τ k *ᵥ x) : S.toSubmodule) i =
        ρ k (e (b.equivFun.symm x : S.toSubmodule) i)
      have hm : b.equivFun.symm (τ k *ᵥ x) =
          S.toRepresentation k (b.equivFun.symm x) :=
        KFiniteDual.equivFun_symm_coordRep S k x
      rw [hm]
      exact he k _ i⟩
  let wS : S.toSubmodule := ⟨w, FiniteVectors.self_mem_orbitSpan κ w⟩
  have hv : (fun i => (q i).val (b.equivFun wS)) = e w := by
    funext i
    change e (b.equivFun.symm (b.equivFun wS) : S.toSubmodule) i = e w i
    rw [LinearEquiv.symm_apply_apply]
  rw [← hv]
  exact finiteDimensional_span_range_intertwiners ρ hρ d τ
    (KFiniteDual.continuous_subMatrix hκ S) q (b.equivFun wS)

end Langlands.Archimedean
