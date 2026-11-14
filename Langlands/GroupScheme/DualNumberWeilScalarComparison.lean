import Langlands.GroupScheme.DualNumberWeilScalarKernel
import Langlands.GroupScheme.VectorScalarKernel
import Langlands.GroupScheme.CorepresentedAffineComparison

/-! # Scalar multiplication and its actual Weil restriction -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2000
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace VectorGroup

variable {R : CommRingCat.{u}} {n : ℕ}

/-- Affine algebra coordinates recover the same scalar as all-test coordinates. -/
theorem affinePointsEquiv_scalar (c : R) (T : CommAlgCat R)
    (p : (algSpec R).obj (op T) ⟶ (groupScheme R n).X) (i : Fin n) :
    (Corepresented.affinePointsEquiv (functor R n) (corepresentableBy R n) T
      (p ≫ (scalar c).hom.hom)).toAdd i =
      algebraMap R T c *
        (Corepresented.affinePointsEquiv (functor R n) (corepresentableBy R n) T p).toAdd i := by
  have h := congrArg (fun x => x.toAdd i)
    (Corepresented.map_affineSectionsIso_pointsEquiv
      (functor R n) (corepresentableBy R n) T (p ≫ (scalar c).hom.hom))
  have hp := congrArg (fun x => x.toAdd i)
    (Corepresented.map_affineSectionsIso_pointsEquiv
      (functor R n) (corepresentableBy R n) T p)
  change (Corepresented.affineSectionsIso T).hom.hom
      ((coordinates R n ((algSpec R).obj (op T)) (p ≫ (scalar c).hom.hom)).toAdd i) = _ at h
  change (Corepresented.affineSectionsIso T).hom.hom
      ((coordinates R n ((algSpec R).obj (op T)) p).toAdd i) = _ at hp
  rw [coordinates_scalar, map_mul] at h
  have hc :
      (Corepresented.affineSectionsIso T).hom.hom
        (scalarMap ((algSpec R).obj (op T)) c) = algebraMap R T c :=
    (Corepresented.affineSectionsIso T).hom.hom.commutes c
  rw [hc, hp] at h
  exact h.symm

end VectorGroup

namespace DualNumberWeil

variable (k : Type u) [Field k] (c : DualNumber k)

local instance : Module.Finite k (DualNumber k) := by
  change Module.Finite k (k × k)
  infer_instance

local instance : Module.Projective k (DualNumber k) := by
  change Module.Projective k (k × k)
  infer_instance

local instance :
    IsAffine (VectorGroup.groupScheme (CommRingCat.of (DualNumber k)) 1).X.left := by
  change IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin 1) (DualNumber k))))
  infer_instance

local instance :
    LocallyOfFiniteType (VectorGroup.groupScheme (CommRingCat.of (DualNumber k)) 1).X.hom := by
  have : Smooth (VectorGroup.groupScheme (CommRingCat.of (DualNumber k)) 1).X.hom :=
    Corepresented.smooth_groupScheme_iff.mpr inferInstance
  infer_instance

/-- The original additive scalar map restricted by the actual affine Weil functor. -/
def restrictedScalar : groupScheme k ⟶ groupScheme k :=
  AffineWeil.map k (DualNumber k)
    (VectorGroup.scalar (R := CommRingCat.of (DualNumber k)) (n := 1) c)

variable {T : Type u} [CommRing T] [Algebra k T]

/-- The tensor scalar from the original dual-number base has the expected coefficients. -/
theorem tensorEquiv_includeLeft :
    tensorEquiv k T
      (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := DualNumber k) (B := T) c) =
      GeneralLinear.DualNumber.coefficientMap (algebraMap k T) c := by
  change tensorEquiv k T (c ⊗ₜ[k] (1 : T)) = _
  rw [tensorEquiv_tmul]
  simp

/-- On affine algebra points, restriction of the original scalar acts by that scalar. -/
theorem affineCoordinates_scalar
    (p : (AffineWeil.pointFunctor k (DualNumber k)
      (VectorGroup.groupScheme (CommRingCat.of (DualNumber k)) 1)).obj
        (CommAlgCat.of (CommRingCat.of k) T)) :
    affineCoordinates k T
      (p ≫ (VectorGroup.scalar (R := CommRingCat.of (DualNumber k)) (n := 1) c).hom.hom) =
      Multiplicative.ofAdd
        (GeneralLinear.DualNumber.coefficientMap (algebraMap k T) c *
          (affineCoordinates k T p).toAdd) := by
  apply Multiplicative.toAdd.injective
  change tensorEquiv k T
      ((Corepresented.affinePointsEquiv
        (VectorGroup.functor (CommRingCat.of (DualNumber k)) 1)
        (VectorGroup.corepresentableBy (CommRingCat.of (DualNumber k)) 1)
        (CommAlgCat.of (CommRingCat.of (DualNumber k)) (DualNumber k ⊗[k] T))
        (p ≫ (VectorGroup.scalar c).hom.hom)).toAdd 0) = _
  rw [VectorGroup.affinePointsEquiv_scalar, map_mul]
  change tensorEquiv k T
      (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := DualNumber k) (B := T) c) *
      tensorEquiv k T _ = _
  rw [tensorEquiv_includeLeft]
  rfl

variable (S : Over (Spec (CommRingCat.of k)))

/-- The actual restricted map has the computed scalar action on every scheme test. -/
theorem coordinates_restrictedScalar (p : S ⟶ (groupScheme k).X) :
    coordinates k S (p ≫ (restrictedScalar k c).hom.hom) =
      Multiplicative.ofAdd (scalarElement k c S * (coordinates k S p).toAdd) := by
  dsimp only [coordinates, MulEquiv.trans_apply, restrictedScalar, AffineWeil.map]
  rw [Corepresented.groupSchemeMap_points]
  exact affineCoordinates_scalar k c _

/-- The computed scalar map is the restriction of the original additive scalar. -/
theorem scalarMap_eq_restrictedScalar : scalarMap k c = restrictedScalar k c := by
  apply hom_ext_points
  intro S p
  apply (coordinates k S).injective
  rw [coordinates_scalarMap, coordinates_restrictedScalar]

/-- The actual restricted scalar kernel is a vector group of the computed dimension. -/
def restrictedScalarKernelIso :
    kernel (restrictedScalar k c) ≅
      VectorGroup.groupScheme (CommRingCat.of k) (scalarKernelDimension k c) := by
  rw [← scalarMap_eq_restrictedScalar]
  exact scalarKernelIso k c

theorem restrictedScalarKernel_properties :
    Smooth (kernel (restrictedScalar k c)).X.hom ∧
      ConnectedSpace (kernel (restrictedScalar k c)).X.left ∧
      IsUnipotent (kernel (restrictedScalar k c)) := by
  rw [← scalarMap_eq_restrictedScalar]
  exact ⟨scalarKernel_smooth k c, scalarKernel_connected k c, scalarKernel_unipotent k c⟩

end DualNumberWeil
end Langlands.GroupScheme
