import Langlands.AlgebraicGeometry.ImaginaryQuadraticEigensheaf
import Langlands.Shimura.Unitary.ImaginaryQuadraticTensorFactorNaturality

/-! # Actual sectionwise imaginary quadratic tensor factors and their sheaf comparison -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite NumberField Algebra
open Langlands.Shimura.ImaginaryQuadratic
open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w

namespace Langlands.Scheme.Modules

variable {S : AlgebraicGeometry.Scheme.{w}}

/-- The scalar algebra on an open is induced by restriction of the given global scalars. -/
@[instance_reducible]
def sectionScalarAlgebra (R : Type*) [CommRing R] [Algebra R Γ(S, ⊤)]
    (U : S.Opens) : Algebra R Γ(S, U) :=
  ((restrictScalar U).comp (algebraMap R Γ(S, ⊤))).toAlgebra

variable (L : Type u) [Field L] [NumberField L] [IsCMField L]
  (K : Type v) [Field K] [CharZero K] [Algebra L K]
  [IsQuadraticExtension ℚ L]
  [Algebra K Γ(S, ⊤)] [Algebra ℚ Γ(S, ⊤)] [IsScalarTower ℚ K Γ(S, ⊤)]
  (M : S.Modules) (ρ : L →+* End M)

local instance (U : S.Opens) : Algebra K Γ(S, U) := sectionScalarAlgebra K U
local instance (U : S.Opens) : Algebra ℚ Γ(S, U) := sectionScalarAlgebra ℚ U

local instance (U : S.Opens) : IsScalarTower ℚ K Γ(S, U) :=
  IsScalarTower.of_algebraMap_eq (fun r =>
    congrArg (restrictScalar U) (IsScalarTower.algebraMap_apply ℚ K Γ(S, ⊤) r))

local instance (U : S.Opens) : Module ℚ Γ(M, U) :=
  Module.compHom Γ(M, U) (algebraMap ℚ Γ(S, U))

local instance (U : S.Opens) : IsScalarTower ℚ Γ(S, U) Γ(M, U) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- Evaluate the actual sheaf action on sections of an open. -/
def sectionFieldAction (U : S.Opens) : L →+* Module.End Γ(S, U) Γ(M, U) where
  toFun t := (ρ t).val.app (op U) |>.hom
  map_one' := by ext x; exact congrArg (fun a : End M => a.app U x) ρ.map_one
  map_mul' a b := by ext x; exact congrArg (fun c : End M => c.app U x) (ρ.map_mul a b)
  map_zero' := by ext x; exact congrArg (fun a : End M => a.app U x) ρ.map_zero
  map_add' a b := by ext x; exact congrArg (fun c : End M => c.app U x) (ρ.map_add a b)

omit [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [CharZero K] [Algebra ℚ Γ(S, ⊤)]
  [IsScalarTower ℚ K Γ(S, ⊤)] in
@[simp]
theorem sectionFieldAction_apply (U : S.Opens) (t : L) (x : Γ(M, U)) :
    sectionFieldAction L M ρ U t x = (ρ t).app U x := rfl

/-- The genuine coordinate scalar-extension module of sections on an open. -/
def sectionTensorFactor (conjugate : Bool) (U : S.Opens) : ModuleCat Γ(S, U) := by
  letI := tensorModule L Γ(S, U) Γ(M, U) (sectionFieldAction L M ρ U)
  letI := factorAlgebra L K Γ(S, U) conjugate
  letI := tensorModuleTower L Γ(S, U) Γ(M, U) (sectionFieldAction L M ρ U)
  letI := factorAlgebraTower L K Γ(S, U) conjugate
  exact ModuleCat.of Γ(S, U) (Γ(S, U) ⊗[Γ(S, U) ⊗[ℚ] L] Γ(M, U))

omit [IsQuadraticExtension ℚ L] [CharZero K] [Algebra ℚ Γ(S, ⊤)]
  [IsScalarTower ℚ K Γ(S, ⊤)] in
/-- The local coordinate character is the restriction of the global coordinate character. -/
theorem sectionFactorCharacter_eq (conjugate : Bool) (U : S.Opens) :
    factorCharacter L K Γ(S, U) conjugate =
      (restrictScalar U).comp (sheafFactorCharacter L K conjugate) := by
  cases conjugate <;> rfl

/-- Identify the actual module eigenconditions with the full eigensheaf sections. -/
def sectionEigenEquiv (conjugate : Bool) (U : S.Opens) :
    eigenmodule L K Γ(S, U) Γ(M, U) (sectionFieldAction L M ρ U) conjugate ≃ₗ[Γ(S, U)]
      Γ(scalarEigensheaf ρ (sheafFactorCharacter L K conjugate), U) where
  toFun x := ⟨x.val, by
    intro t
    have h := x.property t
    simpa only [sectionFactorCharacter_eq L K conjugate U, RingHom.comp_apply,
      sectionFieldAction_apply] using h⟩
  invFun x := ⟨x.val, by
    intro t
    have h := x.property t
    simpa only [sectionFactorCharacter_eq L K conjugate U, RingHom.comp_apply,
      sectionFieldAction_apply] using h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual tensor factor is linearly equivalent to the full eigensheaf sections. -/
def sectionTensorEquiv (conjugate : Bool) (U : S.Opens) :
    sectionTensorFactor L K M ρ conjugate U ≃ₗ[Γ(S, U)]
      Γ(scalarEigensheaf ρ (sheafFactorCharacter L K conjugate), U) := by
  letI := tensorModule L Γ(S, U) Γ(M, U) (sectionFieldAction L M ρ U)
  letI := factorAlgebra L K Γ(S, U) conjugate
  letI := tensorModuleTower L Γ(S, U) Γ(M, U) (sectionFieldAction L M ρ U)
  letI := factorAlgebraTower L K Γ(S, U) conjugate
  exact (tensorFactorEquiv L K Γ(S, U) Γ(M, U) (sectionFieldAction L M ρ U) conjugate).trans
    (sectionEigenEquiv L K M ρ conjugate U)

/-- Restriction of regular functions preserves the induced structural K-scalars. -/
def sectionRestrictionAlgebra {U V : S.Opens} (j : U ⟶ V) :
    Γ(S, V) →ₐ[K] Γ(S, U) where
  __ := (S.presheaf.map j.op).hom
  commutes' r := restrictScalar_map j (algebraMap K Γ(S, ⊤) r)

/-- The canonical map of actual tensor factors induced by restriction of sections. -/
def sectionTensorRestriction (conjugate : Bool) {U V : S.Opens} (j : U ⟶ V) :
    sectionTensorFactor L K M ρ conjugate V →ₛₗ[(S.presheaf.map j.op).hom]
      sectionTensorFactor L K M ρ conjugate U := by
  letI := tensorModule L Γ(S, V) Γ(M, V) (sectionFieldAction L M ρ V)
  letI := factorAlgebra L K Γ(S, V) conjugate
  letI := tensorModuleTower L Γ(S, V) Γ(M, V) (sectionFieldAction L M ρ V)
  letI := factorAlgebraTower L K Γ(S, V) conjugate
  letI := tensorModule L Γ(S, U) Γ(M, U) (sectionFieldAction L M ρ U)
  letI := factorAlgebra L K Γ(S, U) conjugate
  letI := tensorModuleTower L Γ(S, U) Γ(M, U) (sectionFieldAction L M ρ U)
  letI := factorAlgebraTower L K Γ(S, U) conjugate
  exact tensorFactorMap L K Γ(S, V) Γ(S, U) Γ(M, V) Γ(M, U)
    (sectionFieldAction L M ρ V) (sectionFieldAction L M ρ U)
    (sectionRestrictionAlgebra K j) (M.val.restrictₛₗ j.op)
    (fun t x => (PresheafOfModules.naturality_apply (ρ t).val j.op x).symm) conjugate

/-- The sectionwise comparison commutes with the genuine restriction maps. -/
theorem sectionTensorEquiv_restriction (conjugate : Bool) {U V : S.Opens}
    (j : U ⟶ V) (x : sectionTensorFactor L K M ρ conjugate V) :
    sectionTensorEquiv L K M ρ conjugate U (sectionTensorRestriction L K M ρ conjugate j x) =
      (scalarEigensheaf ρ (sheafFactorCharacter L K conjugate)).val.map j.op
        (sectionTensorEquiv L K M ρ conjugate V x) := by
  apply Subtype.ext
  have h :=
    (tensorFactorEquiv_naturality L K Γ(S, V) Γ(S, U) Γ(M, V) Γ(M, U)
      (sectionFieldAction L M ρ V) (sectionFieldAction L M ρ U)
      (sectionRestrictionAlgebra K j) (M.val.restrictₛₗ j.op)
      (fun t x => (PresheafOfModules.naturality_apply (ρ t).val j.op x).symm) conjugate x)
  exact congrArg (fun z :
    eigenmodule L K Γ(S, U) Γ(M, U) (sectionFieldAction L M ρ U) conjugate => z.val) h

/-- Restriction is the canonical map on pure tensors of sections. -/
@[simp]
theorem sectionTensorRestriction_tmul (conjugate : Bool) {U V : S.Opens}
    (j : U ⟶ V) (r : Γ(S, V)) (m : Γ(M, V)) :
    letI := tensorModule L Γ(S, V) Γ(M, V) (sectionFieldAction L M ρ V)
    letI := factorAlgebra L K Γ(S, V) conjugate
    letI := tensorModuleTower L Γ(S, V) Γ(M, V) (sectionFieldAction L M ρ V)
    letI := factorAlgebraTower L K Γ(S, V) conjugate
    letI := tensorModule L Γ(S, U) Γ(M, U) (sectionFieldAction L M ρ U)
    letI := factorAlgebra L K Γ(S, U) conjugate
    letI := tensorModuleTower L Γ(S, U) Γ(M, U) (sectionFieldAction L M ρ U)
    letI := factorAlgebraTower L K Γ(S, U) conjugate
    sectionTensorRestriction L K M ρ conjugate j (r ⊗ₜ[Γ(S, V) ⊗[ℚ] L] m) =
      S.presheaf.map j.op r ⊗ₜ[Γ(S, U) ⊗[ℚ] L]
        (show Γ(M, U) from M.val.restrictₛₗ j.op m) := by
  let := tensorModule L Γ(S, V) Γ(M, V) (sectionFieldAction L M ρ V)
  let := factorAlgebra L K Γ(S, V) conjugate
  let := tensorModuleTower L Γ(S, V) Γ(M, V) (sectionFieldAction L M ρ V)
  let := factorAlgebraTower L K Γ(S, V) conjugate
  let := tensorModule L Γ(S, U) Γ(M, U) (sectionFieldAction L M ρ U)
  let := factorAlgebra L K Γ(S, U) conjugate
  let := tensorModuleTower L Γ(S, U) Γ(M, U) (sectionFieldAction L M ρ U)
  let := factorAlgebraTower L K Γ(S, U) conjugate
  exact tensorFactorMap_tmul L K Γ(S, V) Γ(S, U) Γ(M, V) Γ(M, U)
    (sectionFieldAction L M ρ V) (sectionFieldAction L M ρ U)
    (sectionRestrictionAlgebra K j) (M.val.restrictₛₗ j.op)
    (fun t x => (PresheafOfModules.naturality_apply (ρ t).val j.op x).symm)
    conjugate r m

/-- The actual coordinate tensor factors, with their canonical restriction maps. -/
def tensorFactorPresheaf (conjugate : Bool) : S.PresheafOfModules where
  obj U := sectionTensorFactor L K M ρ conjugate U.unop
  map {U V} f := ModuleCat.semilinearMapAddEquiv _
    (sectionTensorFactor L K M ρ conjugate U.unop)
    (sectionTensorFactor L K M ρ conjugate V.unop)
    (sectionTensorRestriction L K M ρ conjugate f.unop)
  map_id U := by
    ext x
    apply (sectionTensorEquiv L K M ρ conjugate U.unop).injective
    change sectionTensorEquiv L K M ρ conjugate U.unop
        (sectionTensorRestriction L K M ρ conjugate (𝟙 U.unop) x) =
      sectionTensorEquiv L K M ρ conjugate U.unop x
    rw [sectionTensorEquiv_restriction]
    change (scalarEigensheaf ρ (sheafFactorCharacter L K conjugate)).val.map (𝟙 U) _ = _
    rw [PresheafOfModules.map_id]
    rfl
  map_comp {U V W} f g := by
    ext x
    apply (sectionTensorEquiv L K M ρ conjugate W.unop).injective
    change sectionTensorEquiv L K M ρ conjugate W.unop
        (sectionTensorRestriction L K M ρ conjugate (f ≫ g).unop x) =
      sectionTensorEquiv L K M ρ conjugate W.unop
        (sectionTensorRestriction L K M ρ conjugate g.unop
          (sectionTensorRestriction L K M ρ conjugate f.unop x))
    rw [sectionTensorEquiv_restriction, sectionTensorEquiv_restriction,
      sectionTensorEquiv_restriction]
    exact PresheafOfModules.map_comp_apply
      (scalarEigensheaf ρ (sheafFactorCharacter L K conjugate)).val f g _

/-- The constructed comparisons form an actual presheaf-of-modules isomorphism. -/
def tensorFactorPresheafIso (conjugate : Bool) :
    tensorFactorPresheaf L K M ρ conjugate ≅
      (scalarEigensheaf ρ (sheafFactorCharacter L K conjugate)).val :=
  PresheafOfModules.isoMk
    (fun U => (sectionTensorEquiv L K M ρ conjugate U.unop).toModuleIso)
    (by
      intro U V f
      ext x
      exact sectionTensorEquiv_restriction L K M ρ conjugate f.unop x)

/-- The actual tensor-factor presheaf is already a sheaf. -/
def tensorFactorSheaf (conjugate : Bool) : S.Modules where
  val := tensorFactorPresheaf L K M ρ conjugate
  isSheaf := (Presheaf.isSheaf_of_iso_iff
    ((PresheafOfModules.toPresheaf _).mapIso
      (tensorFactorPresheafIso L K M ρ conjugate))).mpr
    (scalarEigensheaf ρ (sheafFactorCharacter L K conjugate)).isSheaf

/-- The actual sectionwise tensor sheaf is the full simultaneous eigensubsheaf. -/
def tensorFactorSheafIso (conjugate : Bool) :
    tensorFactorSheaf L K M ρ conjugate ≅
      scalarEigensheaf ρ (sheafFactorCharacter L K conjugate) :=
  (AlgebraicGeometry.Scheme.Modules.fullyFaithfulToPresheafOfModules (X := S)).preimageIso
    (tensorFactorPresheafIso L K M ρ conjugate)

end Langlands.Scheme.Modules
