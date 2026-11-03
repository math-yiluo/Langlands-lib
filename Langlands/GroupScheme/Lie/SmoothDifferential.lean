import Langlands.GroupScheme.Lie.SubgroupEqualityProof
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Mathlib.Algebra.TrivSqZeroExt.Ideal

/-! # Lifting actual Lie-kernel points along smooth affine homomorphisms -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

section Algebra

variable {R C D A : Type u} [CommRing R] [CommRing C] [CommRing D] [CommRing A]
  [Algebra R C] [Algebra R D] [Algebra R A]

/-- Formal smoothness lifts a compatible dual-number point and its chosen
reduction, with no surjectivity assumption on the original ring map. -/
theorem exists_dualNumberLift_of_formallySmooth (φ : C →ₐ[R] D)
    (hφ : RingHom.FormallySmooth φ.toRingHom)
    (x : C →ₐ[R] DualNumber A) (y : D →ₐ[R] A)
    (hxy : (TrivSqZeroExt.fstHom R A A).comp x = y.comp φ) :
    ∃ z : D →ₐ[R] DualNumber A,
      z.comp φ = x ∧ (TrivSqZeroExt.fstHom R A A).comp z = y := by
  let : Algebra C D := φ.toRingHom.toAlgebra
  let : Algebra C (DualNumber A) := x.toRingHom.toAlgebra
  let : Algebra C A :=
    ((TrivSqZeroExt.fstHom R A A).comp x).toRingHom.toAlgebra
  let : Algebra.FormallySmooth C D := hφ
  let g : DualNumber A →ₐ[C] A :=
    { (TrivSqZeroExt.fstHom R A A).toRingHom with commutes' := fun _ => rfl }
  let y' : D →ₐ[C] A :=
    { y.toRingHom with
      commutes' := fun c => (DFunLike.congr_fun hxy c).symm }
  have hg : Function.Surjective g := TrivSqZeroExt.fst_surjective
  have hnil : IsNilpotent (RingHom.ker g.toRingHom) := by
    refine ⟨2, ?_⟩
    exact TrivSqZeroExt.kerIdeal_sq A A
  let z' := Algebra.FormallySmooth.liftOfSurjective y' g hg hnil
  let z : D →ₐ[R] DualNumber A :=
    { z'.toRingHom with
      commutes' := fun r => by
        rw [← φ.commutes r]
        exact (z'.commutes (algebraMap R C r)).trans (x.commutes r) }
  refine ⟨z, ?_, ?_⟩
  · apply AlgHom.ext
    intro c
    exact z'.commutes c
  · apply AlgHom.ext
    intro d
    exact Algebra.FormallySmooth.liftOfSurjective_apply y' g hg hnil d

end Algebra

section Coordinates

variable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
  [IsAffineHom H.X.hom] [IsAffineHom G.X.hom] (f : H ⟶ G)

/-- Smoothness of an affine group homomorphism is smoothness of its coordinate
restriction homomorphism. -/
theorem restrictionMap_smooth (hf : Smooth f.hom.hom.left) :
    RingHom.Smooth (restrictionMap f).toRingHom := by
  let := hf
  have : IsIso (coordinateIso H).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (coordinateIso H).hom))
  have : IsIso (coordinateIso G).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (coordinateIso G).hom))
  have e : ((algSpec R).map (CommAlgCat.ofHom (restrictionMap f)).op).left ≫
      (coordinateIso G).hom.left = (coordinateIso H).hom.left ≫ f.hom.hom.left := by
    rw [← Over.comp_left, ← Over.comp_left, restrictionMap_spec]
  have h : ((algSpec R).map (CommAlgCat.ofHom (restrictionMap f)).op).left =
      ((coordinateIso H).hom.left ≫ f.hom.hom.left) ≫ inv (coordinateIso G).hom.left := by
    rw [← e, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hs : Smooth ((algSpec R).map (CommAlgCat.ofHom (restrictionMap f)).op).left := by
    rw [h]
    infer_instance
  change Smooth (Spec.map (CommRingCat.ofHom (restrictionMap f).toRingHom)) at hs
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs

variable (A : Type u) [CommRing A] [Algebra R A]

/-- Smooth affine homomorphisms are surjective on actual dual-number identity
kernels over every coefficient algebra. -/
theorem targetMap_surjective_of_smooth (hf : Smooth f.hom.hom.left) :
    Function.Surjective (targetMap f A) := by
  intro X
  obtain ⟨z, hz, hz₀⟩ := exists_dualNumberLift_of_formallySmooth (restrictionMap f)
    (restrictionMap_smooth f hf).formallySmooth (pointCoordinates G X.val)
    ((Algebra.ofId R A).comp (coordinateOrigin H)) (by
      rw [pointCoordinates_kernel, AlgHom.comp_assoc, coordinateOrigin_comp_restrictionMap])
  let Y : lieKernel H A := ⟨(pointCoordinates H).symm z, by
    change reduction H _ = 1
    apply (pointCoordinates H).injective
    change pointCoordinates H (affineMap H (TrivSqZeroExt.fstHom R A A) _) = _
    rw [pointCoordinates_naturality, Equiv.apply_symm_apply, hz₀, pointCoordinates_one]⟩
  refine ⟨Y, ?_⟩
  apply Subtype.ext
  apply (pointCoordinates G).injective
  change pointCoordinates G ((pointCoordinates H).symm z ≫ f.hom.hom) = _
  rw [pointCoordinates_comp_hom, Equiv.apply_symm_apply, hz]

/-- A chosen preimage of an actual infinitesimal identity point under a smooth
affine homomorphism. -/
def smoothKernelLift (hf : Smooth f.hom.hom.left) (X : lieKernel G A) : lieKernel H A :=
  (targetMap_surjective_of_smooth f A hf X).choose

@[simp] theorem targetMap_smoothKernelLift (hf : Smooth f.hom.hom.left)
    (X : lieKernel G A) :
    targetMap f A (smoothKernelLift f A hf X) = X :=
  (targetMap_surjective_of_smooth f A hf X).choose_spec

/-- The differential of a smooth affine homomorphism is surjective over every
coefficient algebra. -/
theorem targetMapLinear_surjective_of_smooth (hf : Smooth f.hom.hom.left) :
    Function.Surjective (targetMapLinear f A) := by
  intro X
  refine ⟨Additive.ofMul (smoothKernelLift f A hf X.toMul), ?_⟩
  exact congrArg Additive.ofMul (targetMap_smoothKernelLift f A hf X.toMul)

end Coordinates

end Langlands.GroupScheme.Lie
