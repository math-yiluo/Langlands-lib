import Langlands.AlgebraicGeometry.ImaginaryQuadraticTensorSheaf
import Langlands.Shimura.PEL.HarrisTaylorLieSplitting

/-! # The actual Harris--Taylor Lie tensor factors in the original tensor order -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite NumberField Algebra
open Langlands.AbelianScheme Langlands.Scheme.Modules
open Langlands.Shimura.ImaginaryQuadratic
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.HarrisTaylor

variable (L : Type) [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L]
  {K : Type} [Field K] [NumberField K] [Algebra L K]
  {S : AlgebraicGeometry.Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of K))
  {A : Type} [Ring A] [Algebra ℚ A] [Algebra K A]
  (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)

local instance [Algebra K Γ(S, ⊤)] (U : S.Opens) : Algebra K Γ(S, U) :=
  sectionScalarAlgebra K U
local instance [Algebra ℚ Γ(S, ⊤)] (U : S.Opens) : Algebra ℚ Γ(S, U) :=
  sectionScalarAlgebra ℚ U
local instance [Algebra K Γ(S, ⊤)] [Algebra ℚ Γ(S, ⊤)]
    [IsScalarTower ℚ K Γ(S, ⊤)] (U : S.Opens) : IsScalarTower ℚ K Γ(S, U) :=
  IsScalarTower.of_algebraMap_eq (fun r =>
    congrArg (restrictScalar U) (IsScalarTower.algebraMap_apply ℚ K Γ(S, ⊤) r))
local instance [Algebra ℚ Γ(S, ⊤)] (U : S.Opens) : Module ℚ Γ(B.Lie, U) :=
  Module.compHom Γ(B.Lie, U) (algebraMap ℚ Γ(S, U))
local instance [Algebra ℚ Γ(S, ⊤)] (U : S.Opens) : IsScalarTower ℚ Γ(S, U) Γ(B.Lie, U) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- The actual Lie-first tensor module on an open, as in the original definition. -/
def lieTensorSections (conjugate : Bool) (U : S.Opens) : ModuleCat Γ(S, U) := by
  letI : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
  letI : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
  letI : IsScalarTower ℚ K Γ(S, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI := tensorModule L Γ(S, U) Γ(B.Lie, U)
    (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U)
  letI := factorAlgebra L K Γ(S, U) conjugate
  letI := tensorModuleTower L Γ(S, U) Γ(B.Lie, U)
    (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U)
  letI := factorAlgebraTower L K Γ(S, U) conjugate
  letI : SMulCommClass (Γ(S, U) ⊗[ℚ] L) Γ(S, U) Γ(B.Lie, U) :=
    IsScalarTower.to_smulCommClass'
  exact ModuleCat.of Γ(S, U) (Γ(B.Lie, U) ⊗[Γ(S, U) ⊗[ℚ] L] Γ(S, U))

/-- Tensor symmetry gives the scalar-first order used by the generic construction. -/
def lieTensorOrderEquiv (conjugate : Bool) (U : S.Opens) :
    letI : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
    letI : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
    letI : IsScalarTower ℚ K Γ(S, ⊤) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    lieTensorSections L s B i conjugate U ≃ₗ[Γ(S, U)]
      sectionTensorFactor L K B.Lie (imaginaryLieAction L s B i) conjugate U := by
  letI : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
  letI : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
  letI : IsScalarTower ℚ K Γ(S, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI := tensorModule L Γ(S, U) Γ(B.Lie, U)
    (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U)
  letI := factorAlgebra L K Γ(S, U) conjugate
  letI := tensorModuleTower L Γ(S, U) Γ(B.Lie, U)
    (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U)
  letI := factorAlgebraTower L K Γ(S, U) conjugate
  letI : SMulCommClass (Γ(S, U) ⊗[ℚ] L) Γ(S, U) Γ(B.Lie, U) :=
    IsScalarTower.to_smulCommClass'
  exact (TensorProduct.comm (Γ(S, U) ⊗[ℚ] L) Γ(B.Lie, U) Γ(S, U)).restrictScalars Γ(S, U)

/-- The actual Lie-first tensor module is the full central Lie eigensheaf on every open. -/
def lieTensorSectionEquiv (conjugate : Bool) (U : S.Opens) :
    letI : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
    letI : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
    letI : IsScalarTower ℚ K Γ(S, ⊤) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    lieTensorSections L s B i conjugate U ≃ₗ[Γ(S, U)]
      Γ(lieEigensheaf L s B i conjugate, U) := by
  letI : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
  letI : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
  letI : IsScalarTower ℚ K Γ(S, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  cases conjugate
  · exact (lieTensorOrderEquiv L s B i false U).trans
      (sectionTensorEquiv L K B.Lie (imaginaryLieAction L s B i) false U)
  · exact (lieTensorOrderEquiv L s B i true U).trans
      (sectionTensorEquiv L K B.Lie (imaginaryLieAction L s B i) true U)


/-- On pure tensors the comparison applies the actual central idempotent projector. -/
@[simp]
theorem lieTensorSectionEquiv_tmul (conjugate : Bool) (U : S.Opens)
    (m : Γ(B.Lie, U)) (r : Γ(S, U)) :
    letI : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
    letI : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
    letI : IsScalarTower ℚ K Γ(S, ⊤) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI := tensorModule L Γ(S, U) Γ(B.Lie, U)
      (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U)
    letI := factorAlgebra L K Γ(S, U) conjugate
    letI := tensorModuleTower L Γ(S, U) Γ(B.Lie, U)
      (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U)
    letI := factorAlgebraTower L K Γ(S, U) conjugate
    (lieTensorSectionEquiv L s B i conjugate U (m ⊗ₜ[Γ(S, U) ⊗[ℚ] L] r)).val =
      r • moduleProjector L K Γ(S, U) Γ(B.Lie, U)
        (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U) conjugate m := by
  cases conjugate <;> rfl

/-- The inverse comparison is the canonical original-order tensor map. -/
theorem lieTensorSectionEquiv_symm_apply (conjugate : Bool) (U : S.Opens)
    (x : Γ(lieEigensheaf L s B i conjugate, U)) :
    letI : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
    letI : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
    letI : IsScalarTower ℚ K Γ(S, ⊤) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI := tensorModule L Γ(S, U) Γ(B.Lie, U)
      (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U)
    letI := factorAlgebra L K Γ(S, U) conjugate
    letI := tensorModuleTower L Γ(S, U) Γ(B.Lie, U)
      (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U)
    letI := factorAlgebraTower L K Γ(S, U) conjugate
    (lieTensorSectionEquiv L s B i conjugate U).symm x =
      (show Γ(B.Lie, U) from x.val) ⊗ₜ[Γ(S, U) ⊗[ℚ] L] (1 : Γ(S, U)) := by
  let : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
  let : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
  let : IsScalarTower ℚ K Γ(S, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let := tensorModule L Γ(S, U) Γ(B.Lie, U)
    (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U)
  let := factorAlgebra L K Γ(S, U) conjugate
  let := tensorModuleTower L Γ(S, U) Γ(B.Lie, U)
    (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U)
  let := factorAlgebraTower L K Γ(S, U) conjugate
  apply (lieTensorSectionEquiv L s B i conjugate U).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [lieTensorSectionEquiv_tmul, one_smul]
  cases conjugate
  · exact (moduleProjector_apply_of_mem L K Γ(S, U) Γ(B.Lie, U)
      (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U) false
      ((sectionEigenEquiv L K B.Lie (imaginaryLieAction L s B i) false U).symm x).property).symm
  · exact (moduleProjector_apply_of_mem L K Γ(S, U) Γ(B.Lie, U)
      (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U) true
      ((sectionEigenEquiv L K B.Lie (imaginaryLieAction L s B i) true U).symm x).property).symm

/-- Restriction transported through the actual tensor/eigen comparison. -/
def lieTensorRestriction (conjugate : Bool) {U V : S.Opens} (j : U ⟶ V) :
    lieTensorSections L s B i conjugate V →ₛₗ[(S.presheaf.map j.op).hom]
      lieTensorSections L s B i conjugate U :=
  (lieTensorSectionEquiv L s B i conjugate U).symm.toLinearMap.comp
    (((lieEigensheaf L s B i conjugate).val.restrictₛₗ j.op).comp
      (lieTensorSectionEquiv L s B i conjugate V).toLinearMap)

/-- The comparison commutes with the constructed restrictions. -/
theorem lieTensorSectionEquiv_restriction (conjugate : Bool) {U V : S.Opens}
    (j : U ⟶ V) (x : lieTensorSections L s B i conjugate V) :
    lieTensorSectionEquiv L s B i conjugate U (lieTensorRestriction L s B i conjugate j x) =
      (lieEigensheaf L s B i conjugate).val.map j.op
        (lieTensorSectionEquiv L s B i conjugate V x) := by
  exact (lieTensorSectionEquiv L s B i conjugate U).apply_symm_apply _

/-- The transported restriction is the canonical restriction on the original-order tensors. -/
@[simp]
theorem lieTensorRestriction_tmul (conjugate : Bool) {U V : S.Opens}
    (j : U ⟶ V) (m : Γ(B.Lie, V)) (r : Γ(S, V)) :
    letI : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
    letI : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
    letI : IsScalarTower ℚ K Γ(S, ⊤) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI := tensorModule L Γ(S, V) Γ(B.Lie, V)
      (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) V)
    letI := factorAlgebra L K Γ(S, V) conjugate
    letI := tensorModuleTower L Γ(S, V) Γ(B.Lie, V)
      (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) V)
    letI := factorAlgebraTower L K Γ(S, V) conjugate
    letI := tensorModule L Γ(S, U) Γ(B.Lie, U)
      (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U)
    letI := factorAlgebra L K Γ(S, U) conjugate
    letI := tensorModuleTower L Γ(S, U) Γ(B.Lie, U)
      (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U)
    letI := factorAlgebraTower L K Γ(S, U) conjugate
    lieTensorRestriction L s B i conjugate j (m ⊗ₜ[Γ(S, V) ⊗[ℚ] L] r) =
      (show Γ(B.Lie, U) from B.Lie.val.restrictₛₗ j.op m) ⊗ₜ[Γ(S, U) ⊗[ℚ] L]
        S.presheaf.map j.op r := by
  let : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
  let : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
  let : IsScalarTower ℚ K Γ(S, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let := tensorModule L Γ(S, V) Γ(B.Lie, V)
    (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) V)
  let := factorAlgebra L K Γ(S, V) conjugate
  let := tensorModuleTower L Γ(S, V) Γ(B.Lie, V)
    (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) V)
  let := factorAlgebraTower L K Γ(S, V) conjugate
  let := tensorModule L Γ(S, U) Γ(B.Lie, U)
    (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U)
  let := factorAlgebra L K Γ(S, U) conjugate
  let := tensorModuleTower L Γ(S, U) Γ(B.Lie, U)
    (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U)
  let := factorAlgebraTower L K Γ(S, U) conjugate
  apply (lieTensorSectionEquiv L s B i conjugate U).injective
  rw [lieTensorSectionEquiv_restriction]
  apply Subtype.ext
  change B.Lie.val.restrictₛₗ j.op
      (lieTensorSectionEquiv L s B i conjugate V (m ⊗ₜ[Γ(S, V) ⊗[ℚ] L] r)).val =
    (lieTensorSectionEquiv L s B i conjugate U
      ((show Γ(B.Lie, U) from B.Lie.val.restrictₛₗ j.op m) ⊗ₜ[Γ(S, U) ⊗[ℚ] L]
        S.presheaf.map j.op r)).val
  rw [lieTensorSectionEquiv_tmul, lieTensorSectionEquiv_tmul, LinearMap.map_smulₛₗ]
  exact congrArg (fun x : Γ(B.Lie, U) => S.presheaf.map j.op r • x)
    (moduleProjector_naturality L K Γ(S, V) Γ(S, U) Γ(B.Lie, V) Γ(B.Lie, U)
      (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) V)
      (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U)
      (sectionRestrictionAlgebra K j) (B.Lie.val.restrictₛₗ j.op)
      (fun t x => (PresheafOfModules.naturality_apply
        (imaginaryLieAction L s B i t).val j.op x).symm) conjugate m)

/-- The Lie-first tensor modules and their actual restrictions form a presheaf. -/
def lieTensorPresheaf (conjugate : Bool) : S.PresheafOfModules where
  obj U := lieTensorSections L s B i conjugate U.unop
  map {U V} f := ModuleCat.semilinearMapAddEquiv _
    (lieTensorSections L s B i conjugate U.unop)
    (lieTensorSections L s B i conjugate V.unop)
    (lieTensorRestriction L s B i conjugate f.unop)
  map_id U := by
    ext x
    apply (lieTensorSectionEquiv L s B i conjugate U.unop).injective
    change lieTensorSectionEquiv L s B i conjugate U.unop
        (lieTensorRestriction L s B i conjugate (𝟙 U.unop) x) =
      lieTensorSectionEquiv L s B i conjugate U.unop x
    rw [lieTensorSectionEquiv_restriction]
    change (lieEigensheaf L s B i conjugate).val.map (𝟙 U) _ = _
    rw [PresheafOfModules.map_id]
    rfl
  map_comp {U V W} f g := by
    ext x
    apply (lieTensorSectionEquiv L s B i conjugate W.unop).injective
    change lieTensorSectionEquiv L s B i conjugate W.unop
        (lieTensorRestriction L s B i conjugate (f ≫ g).unop x) =
      lieTensorSectionEquiv L s B i conjugate W.unop
        (lieTensorRestriction L s B i conjugate g.unop
          (lieTensorRestriction L s B i conjugate f.unop x))
    rw [lieTensorSectionEquiv_restriction, lieTensorSectionEquiv_restriction,
      lieTensorSectionEquiv_restriction]
    exact PresheafOfModules.map_comp_apply (lieEigensheaf L s B i conjugate).val f g _

/-- The constructed Lie-first tensor presheaf is isomorphic to the full Lie eigensheaf. -/
def lieTensorPresheafIso (conjugate : Bool) :
    lieTensorPresheaf L s B i conjugate ≅ (lieEigensheaf L s B i conjugate).val :=
  PresheafOfModules.isoMk
    (fun U => (lieTensorSectionEquiv L s B i conjugate U.unop).toModuleIso)
    (by
      intro U V f
      ext x
      exact lieTensorSectionEquiv_restriction L s B i conjugate f.unop x)

/-- The actual Harris--Taylor Lie-first coordinate tensor sheaf; no sheafification is needed. -/
def lieTensorSheaf (conjugate : Bool) : S.Modules where
  val := lieTensorPresheaf L s B i conjugate
  isSheaf := (Presheaf.isSheaf_of_iso_iff
    ((PresheafOfModules.toPresheaf _).mapIso
      (lieTensorPresheafIso L s B i conjugate))).mpr
    (lieEigensheaf L s B i conjugate).isSheaf

/-- The original-order Lie tensor sheaf is the actual full central eigensubsheaf. -/
def lieTensorSheafIso (conjugate : Bool) :
    lieTensorSheaf L s B i conjugate ≅ lieEigensheaf L s B i conjugate :=
  (AlgebraicGeometry.Scheme.Modules.fullyFaithfulToPresheafOfModules (X := S)).preimageIso
    (lieTensorPresheafIso L s B i conjugate)

@[simp]
theorem lieTensorSheafIso_hom_app (conjugate : Bool) (U : S.Opens)
    (x : Γ(lieTensorSheaf L s B i conjugate, U)) :
    (lieTensorSheafIso L s B i conjugate).hom.app U x =
      lieTensorSectionEquiv L s B i conjugate U x := rfl

@[simp]
theorem lieTensorSheafIso_inv_app (conjugate : Bool) (U : S.Opens)
    (x : Γ(lieEigensheaf L s B i conjugate, U)) :
    (lieTensorSheafIso L s B i conjugate).inv.app U x =
      (lieTensorSectionEquiv L s B i conjugate U).symm x := rfl

/-- The canonical projection onto the actual Lie tensor factor. -/
def lieTensorProjection (conjugate : Bool) : B.Lie ⟶ lieTensorSheaf L s B i conjugate :=
  lieEigenProjection L s B i conjugate ≫ (lieTensorSheafIso L s B i conjugate).inv

/-- The sheaf projector and the actual section-module projector agree. -/
private theorem lieEigenProjection_val_app (conjugate : Bool) (U : S.Opens)
    (m : Γ(B.Lie, U)) :
    letI : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
    letI : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
    letI : IsScalarTower ℚ K Γ(S, ⊤) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    ((lieEigenProjection L s B i conjugate).app U m).val =
      moduleProjector L K Γ(S, U) Γ(B.Lie, U)
        (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U) conjugate m := by
  let : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
  let : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
  let : IsScalarTower ℚ K Γ(S, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let ρ := sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U
  let p := moduleProjector L K Γ(S, U) Γ(B.Lie, U) ρ conjugate m
  let q := moduleProjector L K Γ(S, U) Γ(B.Lie, U) ρ (!conjugate) m
  have hp : p ∈ scalarEigenSections (imaginaryLieAction L s B i)
      (sheafFactorCharacter L K conjugate) U :=
    (sectionEigenEquiv L K B.Lie (imaginaryLieAction L s B i) conjugate U
      ⟨p, moduleProjector_mem L K Γ(S, U) Γ(B.Lie, U) ρ conjugate m⟩).property
  have hq : q ∈ scalarEigenSections (imaginaryLieAction L s B i)
      (sheafFactorCharacter L K (!conjugate)) U :=
    (sectionEigenEquiv L K B.Lie (imaginaryLieAction L s B i) (!conjugate) U
      ⟨q, moduleProjector_mem L K Γ(S, U) Γ(B.Lie, U) ρ (!conjugate) m⟩).property
  have hsum : p + q = m :=
    congrArg (fun f : Module.End Γ(S, U) Γ(B.Lie, U) => f m)
      (moduleProjector_add_other L K Γ(S, U) Γ(B.Lie, U) ρ conjugate)
  have h := congrArg
    (fun x : Γ(B.Lie, U) => (sheafProjector L K B.Lie (imaginaryLieAction L s B i)
      conjugate).app U x) hsum
  rw [map_add, sheafProjector_apply_of_mem L K B.Lie
    (imaginaryLieAction L s B i) conjugate U hp] at h
  have hzero := sheafProjector_other_apply_of_mem L K B.Lie
    (imaginaryLieAction L s B i) (!conjugate) U hq
  simp only [Bool.not_not] at hzero
  rw [hzero, add_zero] at h
  cases conjugate <;> exact h.symm

/-- The Lie projection is exactly the canonical map to the tensor factor. -/
@[simp]
theorem lieTensorProjection_app (conjugate : Bool) (U : S.Opens) (m : Γ(B.Lie, U)) :
    letI : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
    letI : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
    letI : IsScalarTower ℚ K Γ(S, ⊤) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI := tensorModule L Γ(S, U) Γ(B.Lie, U)
      (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U)
    letI := factorAlgebra L K Γ(S, U) conjugate
    letI := tensorModuleTower L Γ(S, U) Γ(B.Lie, U)
      (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U)
    letI := factorAlgebraTower L K Γ(S, U) conjugate
    (lieTensorProjection L s B i conjugate).app U m =
      m ⊗ₜ[Γ(S, U) ⊗[ℚ] L] (1 : Γ(S, U)) := by
  let : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
  let : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
  let : IsScalarTower ℚ K Γ(S, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let := tensorModule L Γ(S, U) Γ(B.Lie, U)
    (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U)
  let := factorAlgebra L K Γ(S, U) conjugate
  let := tensorModuleTower L Γ(S, U) Γ(B.Lie, U)
    (sectionFieldAction L B.Lie (imaginaryLieAction L s B i) U)
  let := factorAlgebraTower L K Γ(S, U) conjugate
  apply (lieTensorSectionEquiv L s B i conjugate U).injective
  change lieTensorSectionEquiv L s B i conjugate U
      ((lieTensorSectionEquiv L s B i conjugate U).symm
        ((lieEigenProjection L s B i conjugate).app U m)) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [lieTensorSectionEquiv_tmul, one_smul]
  exact lieEigenProjection_val_app L s B i conjugate U m

/-- The actual relative Lie sheaf splits into its two original-order tensor factors. -/
def lieTensorSplitting :
    B.Lie ≅ lieTensorSheaf L s B i false ⨯ lieTensorSheaf L s B i true :=
  lieEigenIso L s B i ≪≫
    prod.mapIso (lieTensorSheafIso L s B i false).symm (lieTensorSheafIso L s B i true).symm

@[simp]
theorem lieTensorSplitting_hom :
    (lieTensorSplitting L s B i).hom =
      prod.lift (lieTensorProjection L s B i false) (lieTensorProjection L s B i true) := by
  simp [lieTensorSplitting, lieTensorProjection]

end Langlands.Shimura.HarrisTaylor
