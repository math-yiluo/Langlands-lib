import Langlands.GroupScheme.Lie.FiniteAction
import Langlands.GroupScheme.Lie.GroupAlgebraCoefficientMaps

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

attribute [local instance] coordinateOriginAlgebra

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  [IsAffineHom G.X.hom] {d : ℕ} (c : FiniteCoordinates G d)
  (A : Type u) [CommRing A] [Algebra R A] (M : Type u) [AddCommMonoid M]

theorem kernelCoefficient_smul_constant (m : M) (p : AddMonoidAlgebra A M)
    (x : Additive (lieKernel G A)) :
    kernelCoefficient G A M m
      (p • lieKernelMapLinear G (IsScalarTower.toAlgHom R A (AddMonoidAlgebra A M)) x) =
      p.coeff m • x := by
  apply (kernelDerivationLinearEquiv G (A := A)).injective
  ext z
  rw [kernelCoefficient_apply, map_smul, map_smul]
  simp only [Derivation.smul_apply, kernelDerivationLinearEquiv_map]
  change (p * AddMonoidAlgebra.single 0 (kernelDerivationLinearEquiv G x z)).coeff m =
    p.coeff m * kernelDerivationLinearEquiv G x z
  exact AddMonoidAlgebra.coeff_mul_single_zero _ _ _

theorem FiniteCoordinates.groupAlgebra_expansion
    (x : Additive (lieKernel G (AddMonoidAlgebra A M))) :
    x = ∑ i : Fin d, (c.equiv (.of R (AddMonoidAlgebra A M)) x i) •
      lieKernelMapLinear G (IsScalarTower.toAlgHom R A (AddMonoidAlgebra A M))
        ((c.equiv (.of R A)).symm (Pi.single i 1)) := by
  classical
  apply (c.equiv (.of R (AddMonoidAlgebra A M))).injective
  rw [map_sum]
  have hbase (i : Fin d) :
      c.equiv (.of R (AddMonoidAlgebra A M))
        (lieKernelMapLinear G (IsScalarTower.toAlgHom R A (AddMonoidAlgebra A M))
          ((c.equiv (.of R A)).symm (Pi.single i 1))) = Pi.single i 1 := by
    have h := c.naturality (CommAlgCat.ofHom (R := R)
      (IsScalarTower.toAlgHom R A (AddMonoidAlgebra A M)))
      ((c.equiv (.of R A)).symm (Pi.single i 1))
    refine h.trans ?_
    rw [LinearEquiv.apply_symm_apply]
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Pi.single_eq_same, map_one]
    · simp only [Pi.single_eq_of_ne hji, map_zero]
  simp only [LinearEquiv.map_smul, hbase]
  ext j
  simp [Pi.single_apply]

include c in
theorem FiniteCoordinates.kernelCoefficient_finite
    (x : Additive (lieKernel G (AddMonoidAlgebra A M))) :
    (Function.support (fun m => kernelCoefficient G A M m x)).Finite := by
  classical
  refine (Finset.univ.biUnion (fun i : Fin d =>
    (c.equiv (.of R (AddMonoidAlgebra A M)) x i).coeff.support)).finite_toSet.subset ?_
  intro m hm
  by_contra hn
  apply hm
  change kernelCoefficient G A M m x = 0
  rw [c.groupAlgebra_expansion A M x, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [kernelCoefficient_smul_constant]
  have hi : (c.equiv (.of R (AddMonoidAlgebra A M)) x i).coeff m = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro h
    exact hn (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩)
  rw [hi, zero_smul]

include c in
def FiniteCoordinates.kernelCoefficients :
    Additive (lieKernel G (AddMonoidAlgebra A M)) →ₗ[A]
      (M →₀ Additive (lieKernel G A)) where
  toFun x := Finsupp.ofSupportFinite (fun m => kernelCoefficient G A M m x)
    (c.kernelCoefficient_finite A M x)
  map_add' x y := by
    apply Finsupp.ext
    intro m
    exact map_add (kernelCoefficient G A M m) x y
  map_smul' a x := by
    apply Finsupp.ext
    intro m
    exact map_smul (kernelCoefficient G A M m) a x

@[simp] theorem FiniteCoordinates.kernelCoefficients_apply
    (x : Additive (lieKernel G (AddMonoidAlgebra A M))) (m : M) :
    c.kernelCoefficients A M x m = kernelCoefficient G A M m x := rfl

theorem FiniteCoordinates.kernelCoefficients_reconstruct
    (x : Additive (lieKernel G (AddMonoidAlgebra A M))) :
    (c.kernelCoefficients A M x).sum (fun m y => AddMonoidAlgebra.single m (1 : A) •
      lieKernelMapLinear G (IsScalarTower.toAlgHom R A (AddMonoidAlgebra A M)) y) = x := by
  apply kernelCoefficient_ext G A M
  intro m
  rw [kernelCoefficient_sum_monomials, c.kernelCoefficients_apply]

end Langlands.GroupScheme.Lie
