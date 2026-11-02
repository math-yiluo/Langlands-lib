import Langlands.GroupScheme.Lie.GroupAlgebraCoordinates
import Langlands.GroupScheme.Lie.Adjoint

/-! # Coefficient maps and reconstruction for actual Lie kernels -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]
variable (A : Type u) [CommRing A] [Algebra R A] (M : Type u) [AddCommMonoid M]

attribute [local instance] coordinateOriginAlgebra

local instance coefficientOriginModule : Module (coordinateAlgebra G) (AddMonoidAlgebra A M) :=
  (coordinateOriginAlgebra G (A := AddMonoidAlgebra A M)).toModule

/-- The test-algebra module on a group-algebra Lie kernel restricted to its coefficient ring. -/
instance kernelCoefficientModule : Module A (Additive (lieKernel G (AddMonoidAlgebra A M))) :=
  Module.restrictScalars A (AddMonoidAlgebra A M) _

/-- The scalar tower for this restricted module. -/
instance kernelCoefficientScalarTower :
    IsScalarTower A (AddMonoidAlgebra A M)
      (Additive (lieKernel G (AddMonoidAlgebra A M))) :=
  IsScalarTower.restrictScalars A (AddMonoidAlgebra A M) _

/-- A single coefficient is linear for the coordinate action through the identity. -/
def originCoefficientMap (m : M) : AddMonoidAlgebra A M →ₗ[coordinateAlgebra G] A where
  toFun x := x.coeff m
  map_add' _ _ := rfl
  map_smul' c x := by
    change (AddMonoidAlgebra.single 0 (algebraMap R A (coordinateOrigin G c)) * x).coeff m =
      algebraMap R A (coordinateOrigin G c) * x.coeff m
    exact AddMonoidAlgebra.coeff_single_zero_mul _ _ _

/-- Read one actual Lie coefficient over any coefficient algebra of the original base. -/
def kernelCoefficient (m : M) :
    Additive (lieKernel G (AddMonoidAlgebra A M)) →ₗ[A] Additive (lieKernel G A) where
  toFun x := (kernelDerivationLinearEquiv G (A := A)).symm
    ((originCoefficientMap G A M m).compDer (kernelDerivationLinearEquiv G x))
  map_add' x y := by
    apply (kernelDerivationLinearEquiv G (A := A)).injective
    ext c
    simp [originCoefficientMap]
  map_smul' a x := by
    apply (kernelDerivationLinearEquiv G (A := A)).injective
    ext c
    simp only [LinearEquiv.apply_symm_apply]
    change ((originCoefficientMap G A M m).compDer
      (kernelDerivationLinearEquiv G ((algebraMap A (AddMonoidAlgebra A M) a) • x))) c = _
    rw [map_smul]
    simp only [map_smul, LinearEquiv.apply_symm_apply, RingHom.id_apply]
    change (AddMonoidAlgebra.single 0 a * (kernelDerivationLinearEquiv G x c)).coeff m =
      a * (kernelDerivationLinearEquiv G x c).coeff m
    exact AddMonoidAlgebra.coeff_single_zero_mul _ _ _

@[simp] theorem kernelCoefficient_apply (m : M)
    (x : Additive (lieKernel G (AddMonoidAlgebra A M))) (c : coordinateAlgebra G) :
    kernelDerivationLinearEquiv G (kernelCoefficient G A M m x) c =
      (kernelDerivationLinearEquiv G x c).coeff m := by
  simp [kernelCoefficient, originCoefficientMap]

/-- All coefficients together distinguish actual Lie vectors over a group algebra. -/
theorem kernelCoefficient_ext {x y : Additive (lieKernel G (AddMonoidAlgebra A M))}
    (h : ∀ m, kernelCoefficient G A M m x = kernelCoefficient G A M m y) : x = y := by
  apply (kernelDerivationLinearEquiv G).injective
  apply Derivation.ext
  intro c
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro m
  simpa only [kernelCoefficient_apply] using
    congrArg (fun z => kernelDerivationLinearEquiv G z c) (h m)

/-- Kernel maps act on identity derivations by applying the algebra homomorphism. -/
@[simp] theorem kernelDerivationLinearEquiv_map {B C : Type u}
    [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
    (f : B →ₐ[R] C) (x : Additive (lieKernel G B)) (c : coordinateAlgebra G) :
    kernelDerivationLinearEquiv G (lieKernelMapLinear G f x) c =
      f (kernelDerivationLinearEquiv G x c) :=
  kernelDerivationEquiv_naturality G f x.toMul c

variable {A M}

open Classical in
/-- A monomial times a constant Lie vector has the expected single coefficient. -/
@[simp] theorem kernelCoefficient_monomial (m n : M) (a : A)
    (x : Additive (lieKernel G A)) :
    kernelCoefficient G A M m
      (AddMonoidAlgebra.single n a •
        lieKernelMapLinear G (IsScalarTower.toAlgHom R A (AddMonoidAlgebra A M)) x) =
      if n = m then a • x else 0 := by
  classical
  apply (kernelDerivationLinearEquiv G (A := A)).injective
  ext c
  rw [kernelCoefficient_apply, map_smul]
  simp only [Derivation.smul_apply, kernelDerivationLinearEquiv_map]
  change (AddMonoidAlgebra.single n a *
    AddMonoidAlgebra.single 0 (kernelDerivationLinearEquiv G x c)).coeff m = _
  simp only [AddMonoidAlgebra.single_mul_single, add_zero, AddMonoidAlgebra.coeff_single]
  by_cases h : n = m
  · subst m
    simp
  · simp [h, Ne.symm h]

variable {B : Type u} [CommRing B] [Algebra R B]

/-- Changing coefficient algebra commutes with reading a Lie coefficient. -/
theorem kernelCoefficient_map (f : A →ₐ[R] B) (m : M)
    (x : Additive (lieKernel G (AddMonoidAlgebra A M))) :
    kernelCoefficient G B M m
        (lieKernelMapLinear G (AddMonoidAlgebra.mapAlgHom M f) x) =
      lieKernelMapLinear G f (kernelCoefficient G A M m x) := by
  apply (kernelDerivationLinearEquiv G (A := B)).injective
  apply Derivation.ext
  intro c
  simp only [kernelCoefficient_apply, kernelDerivationLinearEquiv_map,
    AddMonoidAlgebra.coeff_mapAlgHom]

/-- Finite generation of the coordinates bounds all nonzero Lie coefficients. -/
theorem kernelCoefficient_finite [LocallyOfFiniteType G.X.hom]
    (x : Additive (lieKernel G (AddMonoidAlgebra A M))) :
    (Function.support (fun m => kernelCoefficient G A M m x)).Finite := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := coordinateAlgebra G)
  refine (s.biUnion (fun c => (kernelDerivationLinearEquiv G x c).coeff.support)).finite_toSet.subset ?_
  intro m hm
  by_contra h
  apply hm
  apply (kernelDerivationLinearEquiv G (A := A)).injective
  apply Derivation.ext_of_adjoin_eq_top (s : Set (coordinateAlgebra G)) hs
  intro c hc
  simp only [kernelCoefficient_apply, map_zero, Derivation.zero_apply]
  by_contra hic
  exact h (Finset.mem_biUnion.mpr ⟨c, hc, Finsupp.mem_support_iff.mpr hic⟩)

/-- All Lie coefficients, over an arbitrary test algebra, as a finite linear family. -/
def kernelCoefficients [LocallyOfFiniteType G.X.hom] :
    Additive (lieKernel G (AddMonoidAlgebra A M)) →ₗ[A]
      (M →₀ Additive (lieKernel G A)) where
  toFun x := Finsupp.ofSupportFinite (fun m => kernelCoefficient G A M m x)
    (kernelCoefficient_finite G x)
  map_add' x y := by
    apply Finsupp.ext
    intro m
    exact map_add (kernelCoefficient G A M m) x y
  map_smul' a x := by
    apply Finsupp.ext
    intro m
    exact map_smul (kernelCoefficient G A M m) a x

@[simp] theorem kernelCoefficients_apply [LocallyOfFiniteType G.X.hom]
    (x : Additive (lieKernel G (AddMonoidAlgebra A M))) (m : M) :
    kernelCoefficients G x m = kernelCoefficient G A M m x := rfl

/-- Monomial assembly is inverse to coefficient extraction. -/
theorem kernelCoefficient_sum_monomials (p : M →₀ Additive (lieKernel G A)) (m : M) :
    kernelCoefficient G A M m
      (p.sum fun n y => AddMonoidAlgebra.single n (1 : A) •
        lieKernelMapLinear G (IsScalarTower.toAlgHom R A (AddMonoidAlgebra A M)) y) =
      p m := by
  classical
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
      rw [Finsupp.sum_add_index]
      · simp only [map_add, hp, hq, Finsupp.add_apply]
      · intro n; simp
      · intro n y z; simp [smul_add]
  | single n y =>
      rw [Finsupp.sum_single_index (by simp)]
      rw [kernelCoefficient_monomial]
      by_cases h : n = m
      · subst m; simp
      · simp [h, Ne.symm h]

/-- Every Lie vector over a group algebra is the finite sum of its monomial coefficients. -/
theorem kernelCoefficients_reconstruct [LocallyOfFiniteType G.X.hom]
    (x : Additive (lieKernel G (AddMonoidAlgebra A M))) :
    (kernelCoefficients G x).sum (fun m y => AddMonoidAlgebra.single m (1 : A) •
      lieKernelMapLinear G (IsScalarTower.toAlgHom R A (AddMonoidAlgebra A M)) y) = x := by
  apply kernelCoefficient_ext G A M
  intro m
  rw [kernelCoefficient_sum_monomials, kernelCoefficients_apply]

/-- Constant adjoint actions commute with each individual group-algebra coefficient. -/
theorem kernelCoefficient_adjoint [LocallyOfFiniteType G.X.hom]
    (g : AffinePoints G A) (m : M)
    (x : Additive (lieKernel G (AddMonoidAlgebra A M))) :
    kernelCoefficient G A M m
        (adjoint G (AddMonoidAlgebra A M)
          (affineMap G (IsScalarTower.toAlgHom R A (AddMonoidAlgebra A M)) g) x) =
      adjoint G A g (kernelCoefficient G A M m x) := by
  classical
  have hsum (p : M →₀ Additive (lieKernel G A)) :
      kernelCoefficient G A M m
          (adjoint G (AddMonoidAlgebra A M)
            (affineMap G (IsScalarTower.toAlgHom R A (AddMonoidAlgebra A M)) g)
            (p.sum fun n y => AddMonoidAlgebra.single n (1 : A) •
              lieKernelMapLinear G (IsScalarTower.toAlgHom R A (AddMonoidAlgebra A M)) y)) =
        adjoint G A g (p m) := by
    induction p using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq =>
        rw [Finsupp.sum_add_index]
        · simp only [map_add, hp, hq, Finsupp.add_apply]
        · intro n; simp
        · intro n y z; simp [smul_add]
    | single n y =>
        rw [Finsupp.sum_single_index (by simp), map_smul, ← adjoint_naturality,
          kernelCoefficient_monomial]
        by_cases h : n = m
        · subst m; simp
        · simp [h, Ne.symm h]
  simpa only [kernelCoefficients_reconstruct, kernelCoefficients_apply] using
    hsum (kernelCoefficients G x)

end Langlands.GroupScheme.Lie
