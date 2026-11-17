import Langlands.GroupScheme.Reductive.AffinePinnedScalarExtension
import Langlands.GroupScheme.Reductive.AffinePinnedLocalPinning
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.GroupScheme.Lie.ElementCentralizer

/-! # Coefficient pinning equations on all affine tests -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

local instance (M : AffinePinnedModel.{u}) (A : Type u)
    [CommRing A] [Algebra M.ring A] :
    IsAffineHom (M.groupOver (algebraBaseMap M.ring A)).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd M.group.X.hom (algebraBaseMap M.ring A)))

/-- The actual affine base-map equation supplies the missing scalar tower. -/
theorem scalarTower_of_test {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B]
    (a : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A))
    (ha : algebraBaseMap A B = a)
    (hb : algebraBaseMap R B = a ≫ algebraBaseMap R A) :
    IsScalarTower R A B := by
  apply IsScalarTower.of_algebraMap_eq'
  have h := congrArg (fun f => (Spec.preimage f).hom) hb
  rw [← ha] at h
  simpa only [algebraBaseMap, ← Spec.map_comp, Spec.preimage_map,
    CommRingCat.hom_comp, CommRingCat.hom_ofHom] using h

/-- Coefficient extension of the scalar model's chosen vector is the actual
pinning point of the original model over the same affine test. -/
theorem scalarExtension_pinning_map_point
    (M : AffinePinnedModel.{u}) (A B : Type u)
    [CommRing A] [CommRing B] [Algebra M.ring A] [Algebra M.ring B]
    [Algebra A B] [IsScalarTower M.ring A B]
    (a : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A))
    (ha : algebraBaseMap A B = a)
    (hb : algebraBaseMap M.ring B = a ≫ algebraBaseMap M.ring A)
    (s : M.basis.support) :
    (lieKernelMapLinear (M.groupOver (algebraBaseMap M.ring A))
      (Algebra.ofId A B) ((M.scalarExtension A).pinning s 1).val).toMul.val.left =
        M.rootVectorPoint (algebraBaseMap M.ring A) B a hb s := by
  have hA : Lie.kernelBaseChangeLinearEquiv M.ring A M.group A
      ((M.scalarExtension A).pinning s 1).val =
        lieKernelMapLinear M.group (Algebra.ofId M.ring A) (M.pinning s 1).val := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact M.scalarExtension_pinning_fst A s
  have hn := Lie.kernelBaseChangeLinearEquiv_naturality M.ring A M.group
    (Algebra.ofId A B) ((M.scalarExtension A).pinning s 1).val
  rw [hA] at hn
  have hcomp : ((Algebra.ofId A B).restrictScalars M.ring).comp
      (Algebra.ofId M.ring A) = Algebra.ofId M.ring B := by
    ext
  have hn' := congrArg (fun X => X.toMul.val.left) hn
  change (Lie.affineBaseChangeEquiv M.ring A M.group (DualNumber B) _).left =
    (lieKernelMap M.group ((Algebra.ofId A B).restrictScalars M.ring)
      (lieKernelMap M.group (Algebra.ofId M.ring A) (M.pinning s 1).val.toMul)).val.left at hn'
  rw [Lie.affineBaseChangeEquiv_left] at hn'
  rw [← lieKernelMap_comp, hcomp] at hn'
  apply pullback.hom_ext
  · exact hn'.trans (M.rootVectorPoint_fst _ _ _ hb s).symm
  · change _ ≫ (M.groupOver (algebraBaseMap M.ring A)).X.hom = _
    rw [Over.w]
    change algebraBaseMap A (DualNumber B) =
      M.rootVectorPoint (algebraBaseMap M.ring A) B a hb s ≫
        (M.groupOver (algebraBaseMap M.ring A)).X.hom
    rw [rootVectorPoint_snd, ← ha]
    simp only [algebraBaseMap, ← Spec.map_comp]
    rfl

/-- Equality of the actual chosen differential vectors over the common
coefficient ring implies the pinning equations on every local affine test. -/
theorem preservesLocalPinning_of_coefficient_vectors
    (M N : AffinePinnedModel.{u}) (A : Type u) [CommRing A]
    [Algebra M.ring A] [Algebra N.ring A]
    (e : Comparison (algebraBaseMap M.ring A) (algebraBaseMap N.ring A))
    (σ : M.basis.support ≃ N.basis.support)
    (hv : ∀ s, Lie.targetMapLinear e.hom A ((M.scalarExtension A).pinning s 1).val =
      ((N.scalarExtension A).pinning (σ s) 1).val) :
    PreservesLocalPinning e := by
  intro B _ _ _ _ a ha hb
  let : Algebra A B := (Spec.preimage a).hom.toAlgebra
  have hA : algebraBaseMap A B = a := Spec.map_preimage a
  let : IsScalarTower M.ring A B := scalarTower_of_test a hA ha
  let : IsScalarTower N.ring A B := scalarTower_of_test a hA hb
  refine ⟨σ, fun s => ?_⟩
  have hn := lieKernelTargetLinear_map e.hom (Algebra.ofId A B)
    ((M.scalarExtension A).pinning s 1).val
  rw [hv s] at hn
  have hp := congrArg (fun X => X.toMul.val.left) hn
  simpa only [lieKernelTargetLinear_val, Over.comp_left,
    scalarExtension_pinning_map_point M A B a hA ha s,
    scalarExtension_pinning_map_point N A B a hA hb (σ s)] using hp

/-- The all-local-test consequence of a coefficient differential equation. -/
def CoefficientPinningCriterion : Prop :=
  ∀ (M N : AffinePinnedModel.{u}) (A : Type u) [CommRing A]
    [Algebra M.ring A] [Algebra N.ring A]
    (e : Comparison (algebraBaseMap M.ring A) (algebraBaseMap N.ring A))
    (σ : M.basis.support ≃ N.basis.support),
    (∀ s, Lie.targetMapLinear e.hom A ((M.scalarExtension A).pinning s 1).val =
      ((N.scalarExtension A).pinning (σ s) 1).val) → PreservesLocalPinning e

theorem coefficientPinningCriterion : CoefficientPinningCriterion.{u} :=
  preservesLocalPinning_of_coefficient_vectors

end Langlands.GroupScheme.AffinePinnedModel
