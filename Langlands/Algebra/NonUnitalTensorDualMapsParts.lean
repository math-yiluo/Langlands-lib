import Langlands.Algebra.NonUnitalTensorDualMaps

/-! # Preservation and actual-part restrictions of tensor-dual evaluation -/

set_option autoImplicit false
noncomputable section
namespace Langlands.Algebra.NonUnitalTensorDualMaps
open MulOpposite
open NonUnitalModuleTensor (Tensor tmul)
universe uS uR uX uM
attribute [local instance] NondegenerateTensorScalars.opIsScalarTower
  NondegenerateTensorScalars.opSMulCommClass
variable {S : Type uS} {R : Type uR} {X : Type uX} {M : Type uM}
  [NonUnitalRing S] [NonUnitalRing R]
  [Module ℂ S] [IsScalarTower ℂ S S] [SMulCommClass ℂ S S]
  [Module ℂ R] [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
  [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
  [AddCommGroup M] [NonUnitalModule R M]
  (hS : IsIdempotented S) (hR : IsIdempotented R)
  (hX : ActionsCommute S R X) (hSX : IsNondegenerate S X)
  (hRX : IsNondegenerate Rᵐᵒᵖ X) (hM : IsNondegenerate R M)

local notation "F" => FullDual (M := M) hS hX hSX
local notation "H" => Hom (X := X) hR hM
local notation "DT" => Dual (M := M) hS hX hSX
local notation "HS" => NonUnitalBimoduleTensor.leftModule hX M
local notation "hT" => NondegenerateTensorFunctor.isNondegenerate hS hX hSX M

/-- Precisely the published full dual action of the residual original S-action. -/
abbrev fullAction : NonUnitalModule Sᵐᵒᵖ F :=
  letI := HS
  NonUnitalModuleDual.fullAction hS hT

/-- Precisely the original right-source residual Hom action. -/
abbrev homAction : NonUnitalModule Sᵐᵒᵖ H :=
  letI := NonUnitalModuleDual.dualAction hR hM
  NonUnitalBimoduleHomActions.rightSourceAction hX

/-- The usual pointwise Module on this exact full dual. -/
abbrev fullCoefficients : Module ℂ F :=
  letI := HS
  letI := NondegenerateScalars.module ℂ hS hT
  inferInstance

/-- Exactly the published pointwise Hom coefficient Module. -/
abbrev homCoefficients : Module ℂ H :=
  letI := NonUnitalModuleDual.dualAction hR hM
  NondegenerateModuleHomScalars.homModule ℂ hR.op
    (NonUnitalModuleDual.isNondegenerate hR hM)

/-- Exactly the actual residual nondegenerate Hom part. -/
abbrev HomPart :=
  letI := homAction hR hX hM
  nondegeneratePart hS.op H

local notation "HP" => HomPart hS hR hX hM

/-- The inherited original action on the actual Hom part. -/
abbrev partAction : NonUnitalModule Sᵐᵒᵖ HP :=
  letI := homAction hR hX hM
  inferInstance

/-- The published named pointwise coefficients on the exact part subtype. -/
abbrev partCoefficients : Module ℂ HP :=
  letI := NonUnitalModuleDual.dualAction hR hM
  NonUnitalBimoduleHomScalars.rightSourcePartModule ℂ hS hR hX
    (NonUnitalModuleDual.isNondegenerate hR hM)

/-- Exactly the published inherited original dual action. -/
abbrev dualAction : NonUnitalModule Sᵐᵒᵖ DT :=
  letI := HS
  NonUnitalModuleDual.dualAction hS hT

/-- Exactly the published named pointwise Module on the tensor dual part. -/
abbrev dualCoefficients : Module ℂ DT :=
  letI := HS
  NonUnitalModuleDual.dualModule hS hT

variable (hc : NonUnitalBimoduleTensorScalars.InputCompatible ℂ (S := S) hR hRX)
local notation "C" => curry hS hR hX hSX hRX hM hc
local notation "U" => uncurry hS hR hX hSX hRX hM hc

omit [Module ℂ R] [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] in
/-- Extensionality on all original pure tensors. -/
theorem full_ext {ell k : F}
    (h : ∀ x m, ell (tmul R X M x m) = k (tmul R X M x m)) : ell = k := by
  let := HS
  let := NondegenerateScalars.module ℂ hS hT
  exact LinearMap.toAddMonoidHom_injective (NonUnitalModuleTensor.hom_ext R h)

/-- The actual ambient curry as an additive map. -/
def curryAdd : F →+ H where
  toFun := C
  map_zero' := by
    let := NondegenerateScalars.module ℂ hR hM
    apply NonUnitalModuleHom.ext
    intro x
    apply Subtype.ext
    exact LinearMap.ext (fun _ => rfl)
  map_add' ell k := by
    let := NondegenerateScalars.module ℂ hR hM
    apply NonUnitalModuleHom.ext
    intro x
    apply Subtype.ext
    exact LinearMap.ext (fun _ => rfl)

/-- The actual ambient uncurry as an additive map. -/
def uncurryAddMap : H →+ F where
  toFun := U
  map_zero' := full_ext hS hX hSX (fun _ _ => rfl)
  map_add' _ _ := full_ext hS hX hSX (fun _ _ => rfl)

/-- Original residual right-S preservation for curry. -/
theorem curry_action (a : Sᵐᵒᵖ) (ell : F) :
    letI := fullAction (M := M) hS hX hSX
    letI := homAction hR hX hM
    C (a • ell) = a • C ell := by
  let := NondegenerateScalars.module ℂ hR hM
  apply NonUnitalModuleHom.ext
  intro x
  apply Subtype.ext
  exact LinearMap.ext (fun _ => rfl)

/-- Original residual right-S preservation for uncurry. -/
theorem uncurry_action (a : Sᵐᵒᵖ) (h : H) :
    letI := fullAction (M := M) hS hX hSX
    letI := homAction hR hX hM
    U (a • h) = a • U h := by
  apply full_ext hS hX hSX
  intro x m
  rfl

/-- Curry is complex linear for the exact full-dual and pointwise Hom Modules. -/
def curryLinear :
    letI := fullCoefficients (M := M) hS hX hSX
    letI := homCoefficients hR hM (X := X)
    F →ₗ[ℂ] H := by
  letI := fullCoefficients (M := M) hS hX hSX
  letI := homCoefficients hR hM (X := X)
  refine { toAddHom := (curryAdd hS hR hX hSX hRX hM hc).toAddHom, map_smul' := ?_ }
  intro c ell
  apply NonUnitalModuleHom.ext
  intro x
  apply Subtype.ext
  let := NondegenerateScalars.module ℂ hR hM
  apply LinearMap.ext
  intro m
  exact (NonUnitalModuleDual.canonical_smul_apply hR hM c (C ell x) m).symm

/-- Uncurry is complex linear for those same named ambient Modules. -/
def uncurryLinear :
    letI := fullCoefficients (M := M) hS hX hSX
    letI := homCoefficients hR hM (X := X)
    H →ₗ[ℂ] F := by
  letI := fullCoefficients (M := M) hS hX hSX
  letI := homCoefficients hR hM (X := X)
  refine
    { toAddHom := (uncurryAddMap hS hR hX hSX hRX hM hc).toAddHom
      map_smul' := ?_ }
  intro c h
  apply full_ext hS hX hSX
  intro x m
  exact NonUnitalModuleDual.canonical_smul_apply hR hM c (h x) m

/-- The coefficient refinement keeps the entire additive curry map. -/
theorem curryLinear_toAddMonoidHom :
    (curryLinear hS hR hX hSX hRX hM hc).toAddMonoidHom =
      curryAdd hS hR hX hSX hRX hM hc := rfl

/-- The coefficient refinement keeps the entire additive uncurry map. -/
theorem uncurryLinear_toAddMonoidHom :
    (uncurryLinear hS hR hX hSX hRX hM hc).toAddMonoidHom =
      uncurryAddMap hS hR hX hSX hRX hM hc := rfl

/-- The actual ambient original-action map underlying curry. -/
def curryHom :
    letI := fullAction (M := M) hS hX hSX
    letI := homAction hR hX hM
    NonUnitalModuleHom Sᵐᵒᵖ F H :=
  letI := fullAction (M := M) hS hX hSX
  letI := homAction hR hX hM
  { toAddMonoidHom := curryAdd hS hR hX hSX hRX hM hc
    map_smul' := curry_action hS hR hX hSX hRX hM hc }

/-- The actual ambient original-action map underlying uncurry. -/
def uncurryHom :
    letI := fullAction (M := M) hS hX hSX
    letI := homAction hR hX hM
    NonUnitalModuleHom Sᵐᵒᵖ H F :=
  letI := fullAction (M := M) hS hX hSX
  letI := homAction hR hX hM
  { toAddMonoidHom := uncurryAddMap hS hR hX hSX hRX hM hc
    map_smul' := uncurry_action hS hR hX hSX hRX hM hc }

/-- A specified original S-idempotent fixes a full functional exactly when it fixes its curry. -/
theorem curry_fixed_iff (e : Idempotent S) (ell : F) :
    letI := fullAction (M := M) hS hX hSX
    letI := homAction hR hX hM
    op (e : S) • ell = ell ↔ op (e : S) • C ell = C ell := by
  constructor
  · intro he
    exact (curry_action hS hR hX hSX hRX hM hc (op (e : S)) ell).symm.trans
      (congrArg C he)
  · intro he
    apply full_ext hS hX hSX
    intro x m
    exact congrArg (fun h : H => (h x).val m) he

/-- The same specified fixer of h fixes its actual quotient lift. -/
theorem uncurry_fixed (e : Idempotent S) (h : H) :
    letI := fullAction (M := M) hS hX hSX
    letI := homAction hR hX hM
    op (e : S) • h = h → op (e : S) • U h = U h := by
  intro he
  exact (uncurry_action hS hR hX hSX hRX hM hc (op (e : S)) h).symm.trans
    (congrArg U he)

/-- The actual curry restricted using the same original fixing idempotent. -/
def curryPart (ell : DT) : HP := by
  letI := fullAction (M := M) hS hX hSX
  letI := homAction hR hX hM
  refine ⟨C ell.val, ?_⟩
  obtain ⟨e, he⟩ := ell.property
  exact ⟨e, (curry_action hS hR hX hSX hRX hM hc (e : Sᵐᵒᵖ) ell.val).symm.trans
    (congrArg C he)⟩

/-- The actual quotient lift restricted using the same original fixing idempotent. -/
def uncurryPart (h : HP) : DT := by
  letI := fullAction (M := M) hS hX hSX
  letI := homAction hR hX hM
  refine ⟨U h.val, ?_⟩
  obtain ⟨e, he⟩ := h.property
  exact ⟨e, (uncurry_action hS hR hX hSX hRX hM hc (e : Sᵐᵒᵖ) h.val).symm.trans
    (congrArg U he)⟩

/-- Entire inclusion composite of the actual restricted curry. -/
theorem curryPart_val_function :
    (fun ell : DT => (curryPart hS hR hX hSX hRX hM hc ell).val) =
      fun ell => C ell.val := rfl

/-- Entire inclusion composite of the actual restricted quotient lift. -/
theorem uncurryPart_val_function :
    (fun h : HP => (uncurryPart hS hR hX hSX hRX hM hc h).val) =
      fun h => U h.val := rfl

@[simp] theorem curryPart_apply (ell : DT) (x : X) (m : M) :
    ((curryPart hS hR hX hSX hRX hM hc ell).val x).val m =
      ell.val (tmul R X M x m) := rfl

@[simp] theorem uncurryPart_tmul (h : HP) (x : X) (m : M) :
    (uncurryPart hS hR hX hSX hRX hM hc h).val (tmul R X M x m) =
      (h.val x).val m := rfl

/-- The restricted curry as an actual original right-S intertwiner. -/
def curryPartHom :
    letI := dualAction (M := M) hS hX hSX
    letI := partAction hS hR hX hM
    NonUnitalModuleHom Sᵐᵒᵖ DT HP := by
  letI := dualAction (M := M) hS hX hSX
  letI := partAction hS hR hX hM
  refine
    { toFun := curryPart hS hR hX hSX hRX hM hc
      map_zero' := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · apply Subtype.ext
    exact (curryAdd hS hR hX hSX hRX hM hc).map_zero
  · intro ell k
    apply Subtype.ext
    exact (curryAdd hS hR hX hSX hRX hM hc).map_add ell.val k.val
  · intro a ell
    apply Subtype.ext
    exact curry_action hS hR hX hSX hRX hM hc a ell.val

/-- The restricted quotient lift as an actual original right-S intertwiner. -/
def uncurryPartHom :
    letI := dualAction (M := M) hS hX hSX
    letI := partAction hS hR hX hM
    NonUnitalModuleHom Sᵐᵒᵖ HP DT := by
  letI := dualAction (M := M) hS hX hSX
  letI := partAction hS hR hX hM
  refine
    { toFun := uncurryPart hS hR hX hSX hRX hM hc
      map_zero' := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · apply Subtype.ext
    exact (uncurryAddMap hS hR hX hSX hRX hM hc).map_zero
  · intro h k
    apply Subtype.ext
    exact (uncurryAddMap hS hR hX hSX hRX hM hc).map_add h.val k.val
  · intro a h
    apply Subtype.ext
    exact uncurry_action hS hR hX hSX hRX hM hc a h.val

/-- The exact original tensor-dual inclusion, with its named inherited actions. -/
abbrev dualInclusion :
    letI := fullAction (M := M) hS hX hSX
    letI := dualAction (M := M) hS hX hSX
    NonUnitalModuleHom Sᵐᵒᵖ DT F :=
  letI := HS
  NonUnitalModuleDual.inclusion hS hT

/-- The exact original residual-Hom-part inclusion. -/
abbrev partInclusion :
    letI := homAction hR hX hM
    letI := partAction hS hR hX hM
    NonUnitalModuleHom Sᵐᵒᵖ HP H :=
  letI := homAction hR hX hM
  (nondegeneratePart hS.op H).subtype

/-- The complete inclusion identity as original-action maps. -/
theorem curryPartHom_inclusion :
    letI := fullAction (M := M) hS hX hSX
    letI := dualAction (M := M) hS hX hSX
    letI := homAction hR hX hM
    letI := partAction hS hR hX hM
    (partInclusion hS hR hX hM).comp (curryPartHom hS hR hX hSX hRX hM hc) =
      (curryHom hS hR hX hSX hRX hM hc).comp (dualInclusion (M := M) hS hX hSX) := rfl

/-- The complete reverse inclusion identity as original-action maps. -/
theorem uncurryPartHom_inclusion :
    letI := fullAction (M := M) hS hX hSX
    letI := dualAction (M := M) hS hX hSX
    letI := homAction hR hX hM
    letI := partAction hS hR hX hM
    (dualInclusion (M := M) hS hX hSX).comp (uncurryPartHom hS hR hX hSX hRX hM hc) =
      (uncurryHom hS hR hX hSX hRX hM hc).comp (partInclusion hS hR hX hM) := rfl

/-- Actual complex-linear refinement for the named dualModule and rightSourcePartModule. -/
def curryPartLinear :
    letI := dualCoefficients (M := M) hS hX hSX
    letI := partCoefficients hS hR hX hM
    DT →ₗ[ℂ] HP := by
  letI := dualCoefficients (M := M) hS hX hSX
  letI := partCoefficients hS hR hX hM
  refine
    { toAddHom := (curryPartHom hS hR hX hSX hRX hM hc).toAddMonoidHom.toAddHom
      map_smul' := ?_ }
  intro c ell
  let := fullCoefficients (M := M) hS hX hSX
  let := homCoefficients hR hM (X := X)
  apply Subtype.ext
  exact (curryLinear hS hR hX hSX hRX hM hc).map_smul c ell.val

/-- Actual complex-linear reverse refinement for those same named Modules. -/
def uncurryPartLinear :
    letI := dualCoefficients (M := M) hS hX hSX
    letI := partCoefficients hS hR hX hM
    HP →ₗ[ℂ] DT := by
  letI := dualCoefficients (M := M) hS hX hSX
  letI := partCoefficients hS hR hX hM
  refine
    { toAddHom := (uncurryPartHom hS hR hX hSX hRX hM hc).toAddMonoidHom.toAddHom
      map_smul' := ?_ }
  intro c h
  let := fullCoefficients (M := M) hS hX hSX
  let := homCoefficients hR hM (X := X)
  apply Subtype.ext
  exact (uncurryLinear hS hR hX hSX hRX hM hc).map_smul c h.val

/-- The entire additive map is unchanged by coefficient refinement. -/
theorem curryPartLinear_toAddMonoidHom :
    (curryPartLinear hS hR hX hSX hRX hM hc).toAddMonoidHom =
      (curryPartHom hS hR hX hSX hRX hM hc).toAddMonoidHom := rfl

/-- The entire reverse additive map is unchanged by coefficient refinement. -/
theorem uncurryPartLinear_toAddMonoidHom :
    (uncurryPartLinear hS hR hX hSX hRX hM hc).toAddMonoidHom =
      (uncurryPartHom hS hR hX hSX hRX hM hc).toAddMonoidHom := rfl

/-- The target dual uses the proved equality of recovered and named coefficients. -/
theorem targetRecoveredCoefficients_eq :
    letI := NonUnitalModuleDual.dualAction hR hM
    NondegenerateScalars.module ℂ hR.op (NonUnitalModuleDual.isNondegenerate hR hM) =
      NonUnitalModuleDual.dualModule hR hM :=
  NonUnitalModuleDual.canonicalModule_eq_dualModule hR hM

include hRX hc in
/-- Recovery from the exact part action equals its published inherited Module. -/
theorem partRecoveredCoefficients_eq :
    letI := homAction hR hX hM
    NondegenerateScalars.module ℂ hS.op
      (nondegeneratePart_isNondegenerate (M := H) hS.op) =
      partCoefficients hS hR hX hM := by
  let := NonUnitalModuleDual.dualAction hR hM
  exact NonUnitalBimoduleHomScalars.rightSourcePartRecoveredModule_eq ℂ hS hR hX
    (NonUnitalModuleDual.isNondegenerate hR hM) hRX hc

/-- Pointwise coefficient preservation uses the named part and dual Modules. -/
theorem curryPart_smul (c : ℂ) (ell : DT) :
    letI := dualCoefficients (M := M) hS hX hSX
    letI := partCoefficients hS hR hX hM
    curryPart hS hR hX hSX hRX hM hc (c • ell) =
      c • curryPart hS hR hX hSX hRX hM hc ell := by
  let := dualCoefficients (M := M) hS hX hSX
  let := partCoefficients hS hR hX hM
  exact (curryPartLinear hS hR hX hSX hRX hM hc).map_smul c ell

/-- Reverse coefficient preservation for those same exact Modules. -/
theorem uncurryPart_smul (c : ℂ) (h : HP) :
    letI := dualCoefficients (M := M) hS hX hSX
    letI := partCoefficients hS hR hX hM
    uncurryPart hS hR hX hSX hRX hM hc (c • h) =
      c • uncurryPart hS hR hX hSX hRX hM hc h := by
  let := dualCoefficients (M := M) hS hX hSX
  let := partCoefficients hS hR hX hM
  exact (uncurryPartLinear hS hR hX hSX hRX hM hc).map_smul c h

/-- The full original inclusion retains the pointwise scalar law for curry. -/
theorem curryPart_smul_val (c : ℂ) (ell : DT) :
    letI := dualCoefficients (M := M) hS hX hSX
    letI := partCoefficients hS hR hX hM
    letI := homCoefficients hR hM (X := X)
    (curryPart hS hR hX hSX hRX hM hc (c • ell)).val =
      c • (curryPart hS hR hX hSX hRX hM hc ell).val := by
  exact congrArg Subtype.val (curryPart_smul hS hR hX hSX hRX hM hc c ell)

/-- The full original inclusion retains the pointwise scalar law for uncurry. -/
theorem uncurryPart_smul_val (c : ℂ) (h : HP) :
    letI := dualCoefficients (M := M) hS hX hSX
    letI := partCoefficients hS hR hX hM
    letI := fullCoefficients (M := M) hS hX hSX
    (uncurryPart hS hR hX hSX hRX hM hc (c • h)).val =
      c • (uncurryPart hS hR hX hSX hRX hM hc h).val := by
  exact congrArg Subtype.val (uncurryPart_smul hS hR hX hSX hRX hM hc c h)

/-- Scalar evaluation on the original pure tensor, after both original inclusions. -/
theorem curryPart_smul_apply (c : ℂ) (ell : DT) (x : X) (m : M) :
    letI := dualCoefficients (M := M) hS hX hSX
    ((curryPart hS hR hX hSX hRX hM hc (c • ell)).val x).val m =
      c • ell.val (tmul R X M x m) := rfl

/-- The reverse scalar evaluation formula on the same original pure tensors. -/
theorem uncurryPart_smul_tmul (c : ℂ) (h : HP) (x : X) (m : M) :
    letI := partCoefficients hS hR hX hM
    (uncurryPart hS hR hX hSX hRX hM hc (c • h)).val (tmul R X M x m) =
      c • (h.val x).val m := by
  exact NonUnitalModuleDual.canonical_smul_apply hR hM c (h.val x) m

end Langlands.Algebra.NonUnitalTensorDualMaps
