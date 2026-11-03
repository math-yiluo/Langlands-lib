import Langlands.AlgebraicGeometry.Picard.DualNumberDeformationScaling
import Langlands.AlgebraicGeometry.Modules.ProperCoherentCohomologyFiniteProof

/-! # The intrinsic field module of ordinary first-order line-bundle classes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.DualNumberThickening

open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules

attribute [local instance] structureSheaf_isQuasicoherent

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- Scalars act by actual pullback along the endomorphism `ε ↦ c ε`. -/
instance deformationSMul :
    SMul k (Additive (DeformationClasses preservation f)) where
  smul c q := Additive.ofMul (scaleClass f preservation c q.toMul)

/-- The scalar operation is the actual pullback operation on bundle classes. -/
lemma smul_deformationClasses (c : k)
    (q : Additive (DeformationClasses preservation f)) :
    c • q = Additive.ofMul (scaleClass f preservation c q.toMul) :=
  rfl

section SeparatedQuasiCompact

variable [IsSeparated f] [QuasiCompact f]

/-- Tensor addition and actual epsilon-scaling pullback form a field module. -/
instance deformationModule :
    Module k (Additive (DeformationClasses preservation f)) :=
  let 𝒰 := CechResolution.orderedAffineCoverOfQuasiCompact f
  let E := deformationH1AddEquiv preservation f 𝒰
  Function.Injective.module k E.toAddMonoidHom E.injective
    (fun c q ↦ deformationH1AddEquiv_scaleClass f preservation 𝒰 c q.toMul)

/-- The actual H¹ comparison is linear for the intrinsic pullback scalar action. -/
def deformationH1LinearEquiv (𝒰 : X.OrderedAffineCover) :
    Additive (DeformationClasses preservation f) ≃ₗ[k]
      (DerivedSections.relativeCohomology f 1).obj (structureSheaf X) :=
  { deformationH1AddEquiv preservation f 𝒰 with
    map_smul' := fun c q ↦
      deformationH1AddEquiv_scaleClass f preservation 𝒰 c q.toMul }

/-- The linear comparison retains the original additive comparison. -/
lemma deformationH1LinearEquiv_apply (𝒰 : X.OrderedAffineCover)
    (q : Additive (DeformationClasses preservation f)) :
    deformationH1LinearEquiv preservation f 𝒰 q =
      deformationH1AddEquiv preservation f 𝒰 q :=
  rfl

/-- A normalized cocycle bundle maps to its actual derived cocycle class. -/
lemma deformationH1LinearEquiv_cocycleDeformationClass (𝒰 : X.OrderedAffineCover)
    (z : CechResolution.allPairsCocycles
      (OModulePresheaf.ofModules f (structureSheaf X)) 𝒰) :
    deformationH1LinearEquiv preservation f 𝒰
        (Additive.ofMul (cocycleDeformationClass preservation f 𝒰 z)) =
      CechResolution.allPairsH1Map f 𝒰 (structureSheaf X) z :=
  deformationH1AddEquiv_cocycleDeformationClass preservation f 𝒰 z

/-- The intrinsic deformation module and actual structure-sheaf H¹ have equal rank. -/
lemma finrank_deformationClasses (𝒰 : X.OrderedAffineCover) :
    Module.finrank k (Additive (DeformationClasses preservation f)) =
      Module.finrank k ((DerivedSections.relativeCohomology f 1).obj (structureSheaf X)) :=
  LinearEquiv.finrank_eq (deformationH1LinearEquiv preservation f 𝒰)

end SeparatedQuasiCompact

/-- Over any field, the intrinsic first-order deformation module of a proper
scheme is finite dimensional. -/
theorem finiteDimensional_deformationClasses [IsProper f] :
    FiniteDimensional k (Additive (DeformationClasses preservation f)) := by
  have hfinite := (properCoherentCohomologyFinite k X f inferInstance (structureSheaf X)
    (CechDegreeOne.isQuasicoherent_unit X) (fun U ↦ by
      change Module.Finite Γ(X, U.1) Γ(X, U.1)
      infer_instance)).1 1
  let := hfinite
  exact Module.Finite.equiv
    (deformationH1LinearEquiv preservation f
      (CechResolution.orderedAffineCoverOfQuasiCompact f)).symm

end Langlands.AlgebraicGeometry.Picard.DualNumberThickening
