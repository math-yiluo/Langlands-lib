import Langlands.AlgebraicGeometry.PointTopology.RingPointBaseChange
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMaps
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Coordinates for actual affine base change

The actual pullback has its canonical tensor-coordinate presentation.
Scalar extension of algebra points is a homeomorphism for evaluation
topologies when the value algebra is a topological ring.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

variable (C D B : Type u) (A : Type v)
variable [CommRing C] [CommRing D] [CommRing B] [CommRing A]
variable [Algebra C D] [Algebra C B] [Algebra C A] [Algebra D A]
variable [IsScalarTower C D A]

namespace AlgPoint

/-- Scalar extension of actual algebra points, using the tensor universal property. -/
def baseChangeEquiv :
    AlgPoint C B A ≃ AlgPoint D (D ⊗[C] B) A :=
  (algHomEquiv.trans (AlgHom.liftEquiv C D B A)).trans algHomEquiv.symm

@[simp] theorem baseChangeEquiv_tmul (p : AlgPoint C B A) (d : D) (b : B) :
    baseChangeEquiv C D B A p (d ⊗ₜ[C] b) = algebraMap D A d * p b := by
  change d • p b = _
  exact Algebra.smul_def d (p b)

@[simp] theorem baseChangeEquiv_symm_apply
    (p : AlgPoint D (D ⊗[C] B) A) (b : B) :
    (baseChangeEquiv C D B A).symm p b = p (1 ⊗ₜ[C] b) := rfl

variable [TopologicalSpace A]

theorem continuous_baseChangeEquiv [IsTopologicalRing A] :
    Continuous (baseChangeEquiv C D B A) := by
  apply (continuous_iff _).mpr
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul d b =>
      simpa only [baseChangeEquiv_tmul] using
        continuous_const.fun_mul (continuous_eval (R := C) (S := A) b)
  | add t₁ t₂ h₁ h₂ =>
      have h : (fun p : AlgPoint C B A =>
          baseChangeEquiv C D B A p (t₁ + t₂)) =
          (fun p => baseChangeEquiv C D B A p t₁ +
            baseChangeEquiv C D B A p t₂) := by
        funext p
        exact map_add (baseChangeEquiv C D B A p).toAlgHom t₁ t₂
      rw [h]
      exact h₁.fun_add h₂

theorem continuous_baseChangeEquiv_symm :
    Continuous (baseChangeEquiv C D B A).symm :=
  (continuous_iff _).mpr (fun b => continuous_eval (1 ⊗ₜ[C] b))

/-- Scalar extension preserves evaluation topology for an actual topological value ring. -/
def baseChangeHomeomorph [IsTopologicalRing A] :
    AlgPoint C B A ≃ₜ AlgPoint D (D ⊗[C] B) A where
  toEquiv := baseChangeEquiv C D B A
  continuous_toFun := continuous_baseChangeEquiv C D B A
  continuous_invFun := continuous_baseChangeEquiv_symm C D B A

end AlgPoint

instance ringBaseChange_isAffine (X : Over (Spec (CommRingCat.of C)))
    [IsAffine X.left] : IsAffine (ringBaseChange C D X).left := by
  change IsAffine (pullback X.hom (Spec.algebraMap C D))
  infer_instance

/-- Base change of an actual spectrum, with the base ring as the left tensor factor. -/
def ringBaseChangeSpectrumIso :
    ringBaseChange C D (ringTest C B) ≅ ringTest D (D ⊗[C] B) :=
  Over.isoMk
    (pullbackSymmetry (Spec.algebraMap C B) (Spec.algebraMap C D) ≪≫
      pullbackSpecIso C D B) (by
        change
          ((pullbackSymmetry (Spec.algebraMap C B) (Spec.algebraMap C D)).hom ≫
            (pullbackSpecIso C D B).hom) ≫
              Spec.algebraMap D (D ⊗[C] B) =
            pullback.snd (Spec.algebraMap C B) (Spec.algebraMap C D)
        rw [Category.assoc, pullbackSpecIso_hom_fst']
        exact pullbackSymmetry_hom_comp_fst _ _)

/-- The canonical affine presentation of actual base change, retaining its `D`-structure. -/
def ringBaseChangeAffineOverIso (X : Over (Spec (CommRingCat.of C)))
    [IsAffine X.left] :
    ringBaseChange C D X ≅
      ringTest D (D ⊗[C] AffineCoordinateRing C X) :=
  ((Over.pullback (Spec.algebraMap C D)).mapIso
    (affineSchemeOverIso C X)) ≪≫
      ringBaseChangeSpectrumIso C D (AffineCoordinateRing C X)

end Langlands.AlgebraicGeometry.PointTopology
