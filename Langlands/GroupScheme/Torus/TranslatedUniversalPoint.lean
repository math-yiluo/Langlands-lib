import Langlands.GroupScheme.Torus.UniversalPoint
import Langlands.GroupScheme.Lie.GroupAlgebraCoefficientMaps

/-! # Translation of the universal split-torus point -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.splitTorus

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}} (I : Type u) [Fintype I] [DecidableEq I]
variable {A : Type u} [CommRing A] [Algebra R A]

/-- Evaluate the coefficients and multiply each universal monomial by its value at `t`. -/
def translatedEvaluation (t : I → Aˣ) :
    AddMonoidAlgebra R (I → ℤ) →ₐ[R] AddMonoidAlgebra A (I → ℤ) :=
  AddMonoidAlgebra.lift R _ (I → ℤ)
    ((AddMonoidAlgebra.of A (I → ℤ)) *
      ((algebraMap A (AddMonoidAlgebra A (I → ℤ))).toMonoidHom.comp
        ((Units.coeHom A).comp (exponentValue I t))))

omit [DecidableEq I] in
@[simp] theorem translatedEvaluation_single (t : I → Aˣ) (m : I → ℤ) (r : R) :
    translatedEvaluation I t (AddMonoidAlgebra.single m r) =
      AddMonoidAlgebra.single m
        (algebraMap R A r * (exponentValue I t (Multiplicative.ofAdd m) : A)) := by
  simp [translatedEvaluation, Algebra.smul_def, AddMonoidAlgebra.of_apply,
    AddMonoidAlgebra.single_mul_single]

omit [DecidableEq I] in
/-- Translation multiplies the coefficient at `m` by the monomial's value at `t`. -/
@[simp] theorem coeff_translatedEvaluation (t : I → Aˣ)
    (x : AddMonoidAlgebra R (I → ℤ)) (m : I → ℤ) :
    (translatedEvaluation I t x).coeff m =
      algebraMap R A (x.coeff m) *
        (exponentValue I t (Multiplicative.ofAdd m) : A) := by
  classical
  have h (p : (I → ℤ) →₀ R) :
      (translatedEvaluation I t (AddMonoidAlgebra.ofCoeff p)).coeff m =
        algebraMap R A (p m) * (exponentValue I t (Multiplicative.ofAdd m) : A) := by
    induction p using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq => simp [hp, hq, add_mul]
    | single n r =>
        change (translatedEvaluation I t (AddMonoidAlgebra.single n r)).coeff m = _
        rw [translatedEvaluation_single]
        by_cases h : n = m
        · subst m; simp
        · simp [Ne.symm h]
  exact h x.coeff

/-- On actual points, translated evaluation is multiplication by the constant point `t`. -/
theorem universalPoint_translatedEvaluation (t : I → Aˣ) :
    Lie.affineMap _ (translatedEvaluation (R := R) I t) (universalPoint (R := R) I) =
      Lie.affineMap _ (IsScalarTower.toAlgHom R A (AddMonoidAlgebra A (I → ℤ)))
          ((algebraPointsEquiv I A).symm t) *
        Lie.affineMap _ (AddMonoidAlgebra.mapAlgHom (I → ℤ) (Algebra.ofId R A))
          (universalPoint (R := R) I) := by
  apply (algebraPointsEquiv I _).injective
  rw [algebraPointsEquiv_naturality, algebraPointsEquiv_universalPoint, map_mul,
    algebraPointsEquiv_naturality, MulEquiv.apply_symm_apply,
    algebraPointsEquiv_naturality, algebraPointsEquiv_universalPoint]
  funext j
  apply Units.ext
  change translatedEvaluation I t (AddMonoidAlgebra.single (Pi.single j 1) 1) =
    AddMonoidAlgebra.single 0 (t j : A) *
      AddMonoidAlgebra.mapAlgHom (I → ℤ) (Algebra.ofId R A)
        (AddMonoidAlgebra.single (Pi.single j 1) 1)
  simp

variable (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]

attribute [local instance] Lie.coordinateOriginAlgebra

omit [DecidableEq I] in
/-- Translation of a Lie vector scales each extended coefficient by its monomial value. -/
theorem kernelCoefficient_translatedEvaluation (t : I → Aˣ) (m : I → ℤ)
    (x : Additive (lieKernel G (AddMonoidAlgebra R (I → ℤ)))) :
    Lie.kernelCoefficient G A (I → ℤ) m
        (lieKernelMapLinear G (translatedEvaluation I t) x) =
      (exponentValue I t (Multiplicative.ofAdd m) : A) •
        lieKernelMapLinear G (Algebra.ofId R A)
          (Lie.kernelCoefficient G R (I → ℤ) m x) := by
  apply (Lie.kernelDerivationLinearEquiv G (A := A)).injective
  apply Derivation.ext
  intro c
  simp only [Lie.kernelCoefficient_apply, Lie.kernelDerivationLinearEquiv_map,
    coeff_translatedEvaluation, map_smul, Derivation.smul_apply, Algebra.smul_def]
  exact mul_comm _ _

end Langlands.GroupScheme.splitTorus
