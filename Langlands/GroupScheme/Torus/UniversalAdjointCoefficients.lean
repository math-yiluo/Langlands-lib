import Langlands.GroupScheme.Torus.TranslatedUniversalPoint

/-! # Finite coefficients of the universal split-torus adjoint action -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.splitTorus

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}} (I : Type u) [Fintype I] [DecidableEq I]
variable (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]
variable (i : splitTorus (Spec R) I ⟶ G)

attribute [local instance] Lie.coordinateOriginAlgebra

private theorem kernelMapLinear_const {A B : Type u}
    [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (X : Additive (lieKernel G R)) :
    lieKernelMapLinear G f (lieKernelMapLinear G (Algebra.ofId R A) X) =
      lieKernelMapLinear G (Algebra.ofId R B) X := by
  apply (Lie.kernelDerivationLinearEquiv G).injective
  apply Derivation.ext
  intro c
  simp only [Lie.kernelDerivationLinearEquiv_map, Algebra.ofId_apply, AlgHom.commutes]

/-- Apply the adjoint action of the actual universal point to a constant Lie vector. -/
def universalAdjoint :
    Additive (lieKernel G R) →ₗ[R]
      Additive (lieKernel G (AddMonoidAlgebra R (I → ℤ))) where
  toFun X := adjoint G _ (universalPoint I ≫ i.hom.hom)
    (lieKernelMapLinear G (Algebra.ofId R _) X)
  map_add' X Y := by simp only [map_add]
  map_smul' c X := by
    simp only [LinearMap.map_smulₛₗ]
    rfl

variable {A : Type u} [CommRing A] [Algebra R A]

/-- Universal adjoint action evaluated by any algebra map. -/
theorem universalAdjoint_map (f : AddMonoidAlgebra R (I → ℤ) →ₐ[R] A)
    (X : Additive (lieKernel G R)) :
    lieKernelMapLinear G f (universalAdjoint I G i X) =
      adjoint G A (Lie.affineMap _ f (universalPoint I) ≫ i.hom.hom)
        (lieKernelMapLinear G (Algebra.ofId R A) X) := by
  change lieKernelMapLinear G f
    (adjoint G _ _ (lieKernelMapLinear G (Algebra.ofId R _) X)) = _
  rw [adjoint_naturality, kernelMapLinear_const]
  rfl

/-- Translation of the universal adjoint action is the corresponding constant adjoint action. -/
theorem universalAdjoint_translatedEvaluation (t : I → Aˣ)
    (X : Additive (lieKernel G R)) :
    lieKernelMapLinear G (translatedEvaluation I t) (universalAdjoint I G i X) =
      adjoint G (AddMonoidAlgebra A (I → ℤ))
        (Lie.affineMap G (IsScalarTower.toAlgHom R A (AddMonoidAlgebra A (I → ℤ)))
          ((algebraPointsEquiv I A).symm t ≫ i.hom.hom))
        (lieKernelMapLinear G
          (AddMonoidAlgebra.mapAlgHom (I → ℤ) (Algebra.ofId R A))
          (universalAdjoint I G i X)) := by
  rw [universalAdjoint_map, universalAdjoint_map, universalPoint_translatedEvaluation]
  simp only [MonObj.mul_comp, map_mul, Module.End.mul_apply]
  rfl

variable [LocallyOfFiniteType G.X.hom]

/-- The finite coefficient family of the actual universal adjoint action. -/
def universalAdjointCoefficients :
    Additive (lieKernel G R) →ₗ[R] ((I → ℤ) →₀ Additive (lieKernel G R)) :=
  (Lie.kernelCoefficients G).comp (universalAdjoint I G i)

@[simp] theorem universalAdjointCoefficients_apply
    (X : Additive (lieKernel G R)) (m : I → ℤ) :
    universalAdjointCoefficients I G i X m =
      Lie.kernelCoefficient G R (I → ℤ) m (universalAdjoint I G i X) := rfl

/-- Each universal adjoint coefficient satisfies its exponent-weight equation over every
test algebra, for the actual dual-number adjoint representation. -/
theorem universalAdjointCoefficients_weight (t : I → Aˣ)
    (X : Additive (lieKernel G R)) (m : I → ℤ) :
    adjoint G A ((algebraPointsEquiv I A).symm t ≫ i.hom.hom)
        (lieKernelMapLinear G (Algebra.ofId R A)
          (universalAdjointCoefficients I G i X m)) =
      (exponentValue I t (Multiplicative.ofAdd m) : A) •
        lieKernelMapLinear G (Algebra.ofId R A)
          (universalAdjointCoefficients I G i X m) := by
  have h := congrArg (Lie.kernelCoefficient G A (I → ℤ) m)
    (universalAdjoint_translatedEvaluation I G i t X)
  rw [kernelCoefficient_translatedEvaluation, Lie.kernelCoefficient_adjoint,
    Lie.kernelCoefficient_map] at h
  exact h.symm

/-- A pure universal weight has only its prescribed coefficient. -/
theorem universalAdjointCoefficients_of_monomial
    (X : Additive (lieKernel G R)) (m : I → ℤ)
    (h : universalAdjoint I G i X =
      AddMonoidAlgebra.single m (1 : R) •
        lieKernelMapLinear G (Algebra.ofId R _) X) :
    universalAdjointCoefficients I G i X = Finsupp.single m X := by
  classical
  apply Finsupp.ext
  intro n
  rw [universalAdjointCoefficients_apply, h]
  have hf : IsScalarTower.toAlgHom R R (AddMonoidAlgebra R (I → ℤ)) =
      Algebra.ofId R (AddMonoidAlgebra R (I → ℤ)) := by ext
  have hk := Lie.kernelCoefficient_monomial G n m (1 : R) X
  rw [hf] at hk
  simpa only [Finsupp.single_apply, one_smul] using hk

omit [LocallyOfFiniteType G.X.hom] in
private theorem universalAdjoint_evaluateOne (X : Additive (lieKernel G R)) :
    lieKernelMapLinear G (evaluateUnits (R := R) I (fun _ => (1 : Rˣ)))
      (universalAdjoint I G i X) = X := by
  have ht : (algebraPointsEquiv (R := R) I R).symm (fun _ => (1 : Rˣ)) = 1 := map_one _
  rw [universalAdjoint_map, universalPoint_evaluateUnits, ht, MonObj.one_comp,
    map_one, Module.End.one_apply]
  apply (Lie.kernelDerivationLinearEquiv G).injective
  apply Derivation.ext
  intro c
  simp only [Lie.kernelDerivationLinearEquiv_map, Algebra.ofId_self, AlgHom.id_apply]

/-- The universal adjoint coefficients sum back to the original actual Lie vector. -/
theorem universalAdjointCoefficients_sum (X : Additive (lieKernel G R)) :
    (universalAdjointCoefficients I G i X).sum (fun _ y => y) = X := by
  have h := congrArg (lieKernelMapLinear G (evaluateUnits (R := R) I (fun _ => (1 : Rˣ))))
    (Lie.kernelCoefficients_reconstruct G (universalAdjoint I G i X))
  rw [universalAdjoint_evaluateOne] at h
  rw [map_finsuppSum] at h
  have hc (y : Additive (lieKernel G R)) :
      lieKernelMapLinear G (Algebra.ofId R R) y = y := by
    apply (Lie.kernelDerivationLinearEquiv G).injective
    apply Derivation.ext
    intro c
    simp only [Lie.kernelDerivationLinearEquiv_map, Algebra.ofId_self, AlgHom.id_apply]
  have hf : IsScalarTower.toAlgHom R R (AddMonoidAlgebra R (I → ℤ)) =
      Algebra.ofId R (AddMonoidAlgebra R (I → ℤ)) := by ext
  rw [hf] at h
  have he (m : I → ℤ) :
      (evaluateUnits (R := R) I (fun _ => (1 : Rˣ))).toRingHom
        (AddMonoidAlgebra.single m 1) = 1 := by
    change evaluateUnits I (fun _ => (1 : Rˣ)) (AddMonoidAlgebra.single m 1) = 1
    simp [exponentValue]
  simpa only [universalAdjointCoefficients, LinearMap.comp_apply,
    LinearMap.map_smulₛₗ, kernelMapLinear_const, hc, he, one_smul] using h

end Langlands.GroupScheme.splitTorus
