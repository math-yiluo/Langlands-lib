import Langlands.Algebra.NonUnitalTensorDualMapsParts

/-! # Interface, instance-selection and example checks for tensor-dual evaluation -/

set_option autoImplicit false
set_option linter.checkUnivs false

noncomputable section
namespace Langlands.Algebra.NonUnitalTensorDualMapsChecks

open MulOpposite
open NonUnitalModuleTensor (Tensor tmul)
open NonUnitalTensorDualMaps

universe uS uR uX uM

attribute [local instance] NondegenerateTensorScalars.opIsScalarTower
  NondegenerateTensorScalars.opSMulCommClass

/-- The complete unapplied ambient curry interface retains four independent universes. -/
private abbrev CurryInterface :=
  {S : Type uS} → {R : Type uR} → {X : Type uX} → {M : Type uM} →
  [NonUnitalRing S] → [NonUnitalRing R] →
  [Module ℂ S] → [IsScalarTower ℂ S S] → [SMulCommClass ℂ S S] →
  [Module ℂ R] → [IsScalarTower ℂ R R] → [SMulCommClass ℂ R R] →
  [AddCommGroup X] → [NonUnitalModule S X] → [NonUnitalModule Rᵐᵒᵖ X] →
  [AddCommGroup M] → [NonUnitalModule R M] →
  (hS : IsIdempotented S) → (hR : IsIdempotented R) →
  (hX : ActionsCommute S R X) → (hSX : IsNondegenerate S X) →
  (hRX : IsNondegenerate Rᵐᵒᵖ X) → (hM : IsNondegenerate R M) →
  NonUnitalBimoduleTensorScalars.InputCompatible ℂ (S := S) hR hRX →
  letI := NonUnitalBimoduleTensor.leftModule hX M
  letI := NonUnitalModuleDual.dualAction hR hM
  NonUnitalModuleDual.FullDual hS
      (NondegenerateTensorFunctor.isNondegenerate hS hX hSX M) →
    NonUnitalModuleHom Rᵐᵒᵖ X (NonUnitalModuleDual.Dual hR hM)

example : CurryInterface.{uS,uR,uX,uM} := @curry
example : CurryInterface.{0,1,2,3} := @curry
example : CurryInterface.{3,2,1,0} := @curry

/-- The complete unapplied quotient-lift direction uses the same original carriers. -/
private abbrev UncurryInterface :=
  {S : Type uS} → {R : Type uR} → {X : Type uX} → {M : Type uM} →
  [NonUnitalRing S] → [NonUnitalRing R] →
  [Module ℂ S] → [IsScalarTower ℂ S S] → [SMulCommClass ℂ S S] →
  [Module ℂ R] → [IsScalarTower ℂ R R] → [SMulCommClass ℂ R R] →
  [AddCommGroup X] → [NonUnitalModule S X] → [NonUnitalModule Rᵐᵒᵖ X] →
  [AddCommGroup M] → [NonUnitalModule R M] →
  (hS : IsIdempotented S) → (hR : IsIdempotented R) →
  (hX : ActionsCommute S R X) → (hSX : IsNondegenerate S X) →
  (hRX : IsNondegenerate Rᵐᵒᵖ X) → (hM : IsNondegenerate R M) →
  NonUnitalBimoduleTensorScalars.InputCompatible ℂ (S := S) hR hRX →
  letI := NonUnitalBimoduleTensor.leftModule hX M
  letI := NonUnitalModuleDual.dualAction hR hM
  NonUnitalModuleHom Rᵐᵒᵖ X (NonUnitalModuleDual.Dual hR hM) →
    NonUnitalModuleDual.FullDual hS
      (NondegenerateTensorFunctor.isNondegenerate hS hX hSX M)

example : UncurryInterface.{uS,uR,uX,uM} := @uncurry
example : UncurryInterface.{0,1,2,3} := @uncurry
example : UncurryInterface.{3,2,1,0} := @uncurry

/-- Complete original-action interface in either restricted direction. -/
private abbrev PartHomInterface (reverse : Bool) :=
  {S : Type uS} → {R : Type uR} → {X : Type uX} → {M : Type uM} →
  [NonUnitalRing S] → [NonUnitalRing R] →
  [Module ℂ S] → [IsScalarTower ℂ S S] → [SMulCommClass ℂ S S] →
  [Module ℂ R] → [IsScalarTower ℂ R R] → [SMulCommClass ℂ R R] →
  [AddCommGroup X] → [NonUnitalModule S X] → [NonUnitalModule Rᵐᵒᵖ X] →
  [AddCommGroup M] → [NonUnitalModule R M] →
  (hS : IsIdempotented S) → (hR : IsIdempotented R) →
  (hX : ActionsCommute S R X) → (hSX : IsNondegenerate S X) →
  (hRX : IsNondegenerate Rᵐᵒᵖ X) → (hM : IsNondegenerate R M) →
  NonUnitalBimoduleTensorScalars.InputCompatible ℂ (S := S) hR hRX →
  letI := NonUnitalBimoduleTensor.leftModule hX M
  let hT := NondegenerateTensorFunctor.isNondegenerate hS hX hSX M
  let DT := NonUnitalModuleDual.Dual hS hT
  letI := NonUnitalModuleDual.dualAction hR hM
  let H := NonUnitalModuleHom Rᵐᵒᵖ X (NonUnitalModuleDual.Dual hR hM)
  letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := NonUnitalModuleDual.Dual hR hM) hX
  let HP := nondegeneratePart hS.op H
  letI := NonUnitalModuleDual.dualAction hS hT
  if reverse then NonUnitalModuleHom Sᵐᵒᵖ HP DT else NonUnitalModuleHom Sᵐᵒᵖ DT HP

example : PartHomInterface.{uS,uR,uX,uM} false := @curryPartHom
example : PartHomInterface.{0,1,2,3} false := @curryPartHom
example : PartHomInterface.{3,2,1,0} false := @curryPartHom
example : PartHomInterface.{uS,uR,uX,uM} true := @uncurryPartHom
example : PartHomInterface.{0,1,2,3} true := @uncurryPartHom
example : PartHomInterface.{3,2,1,0} true := @uncurryPartHom

/-- Complete linear interface uses the named inherited Modules on both actual parts. -/
private abbrev PartLinearInterface (reverse : Bool) :=
  {S : Type uS} → {R : Type uR} → {X : Type uX} → {M : Type uM} →
  [NonUnitalRing S] → [NonUnitalRing R] →
  [Module ℂ S] → [IsScalarTower ℂ S S] → [SMulCommClass ℂ S S] →
  [Module ℂ R] → [IsScalarTower ℂ R R] → [SMulCommClass ℂ R R] →
  [AddCommGroup X] → [NonUnitalModule S X] → [NonUnitalModule Rᵐᵒᵖ X] →
  [AddCommGroup M] → [NonUnitalModule R M] →
  (hS : IsIdempotented S) → (hR : IsIdempotented R) →
  (hX : ActionsCommute S R X) → (hSX : IsNondegenerate S X) →
  (hRX : IsNondegenerate Rᵐᵒᵖ X) → (hM : IsNondegenerate R M) →
  NonUnitalBimoduleTensorScalars.InputCompatible ℂ (S := S) hR hRX →
  letI := NonUnitalBimoduleTensor.leftModule hX M
  let hT := NondegenerateTensorFunctor.isNondegenerate hS hX hSX M
  let DT := NonUnitalModuleDual.Dual hS hT
  letI := NonUnitalModuleDual.dualAction hR hM
  let H := NonUnitalModuleHom Rᵐᵒᵖ X (NonUnitalModuleDual.Dual hR hM)
  letI := NonUnitalBimoduleHomActions.rightSourceAction (Z := NonUnitalModuleDual.Dual hR hM) hX
  let HP := nondegeneratePart hS.op H
  letI := NonUnitalModuleDual.dualModule hS hT
  letI := NonUnitalBimoduleHomScalars.rightSourcePartModule ℂ hS hR hX
    (NonUnitalModuleDual.isNondegenerate hR hM)
  if reverse then HP →ₗ[ℂ] DT else DT →ₗ[ℂ] HP

example : PartLinearInterface.{uS,uR,uX,uM} false := @curryPartLinear
example : PartLinearInterface.{0,1,2,3} false := @curryPartLinear
example : PartLinearInterface.{3,2,1,0} false := @curryPartLinear
example : PartLinearInterface.{uS,uR,uX,uM} true := @uncurryPartLinear
example : PartLinearInterface.{0,1,2,3} true := @uncurryPartLinear
example : PartLinearInterface.{3,2,1,0} true := @uncurryPartLinear

section CompetingStructures

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
local notation "DT" => Dual (M := M) hS hX hSX
local notation "DM" => NonUnitalModuleDual.Dual hR hM
local notation "H" => Hom (X := X) hR hM
local notation "HP" => HomPart hS hR hX hM
local notation "MX" => NondegenerateScalars.module ℂ hR.op hRX
local notation "MM" => NondegenerateScalars.module ℂ hR hM
local notation "MT" => NondegenerateTensorScalars.module ℂ R X M hR hM
local notation "HS" => NonUnitalBimoduleTensor.leftModule hX M

variable [competingX : Module ℂ X] [competingM : Module ℂ M]
  [competingT : Module ℂ (Tensor R X M)]
  [competingHS : NonUnitalModule S (Tensor R X M)]
  [competingDM : Module ℂ (NonUnitalModuleDual.Dual hR hM)]
  [competingDMAction : NonUnitalModule Rᵐᵒᵖ (NonUnitalModuleDual.Dual hR hM)]
  [competingF : Module ℂ (FullDual (M := M) hS hX hSX)]
  [competingFAction : NonUnitalModule Sᵐᵒᵖ (FullDual (M := M) hS hX hSX)]
  [competingDT : Module ℂ (Dual (M := M) hS hX hSX)]
  [competingDTAction : NonUnitalModule Sᵐᵒᵖ (Dual (M := M) hS hX hSX)]
  [competingH : Module ℂ (Hom (X := X) hR hM)]
  [competingHAction : NonUnitalModule Sᵐᵒᵖ (Hom (X := X) hR hM)]
  [competingHP : Module ℂ (HomPart hS hR hX hM)]
  [competingHPAction : NonUnitalModule Sᵐᵒᵖ (HomPart hS hR hX hM)]

/-- Explicit choices select the published structures in the presence of competitors. -/
example :
    letI := MX
    letI := MM
    letI := MT
    letI := HS
    letI := NonUnitalModuleDual.dualAction hR hM
    letI := NonUnitalModuleDual.dualModule hR hM
    letI := fullAction (M := M) hS hX hSX
    letI := fullCoefficients (M := M) hS hX hSX
    letI := dualAction (M := M) hS hX hSX
    letI := dualCoefficients (M := M) hS hX hSX
    letI := homAction hR hX hM
    letI := homCoefficients (X := X) hR hM
    letI := partAction hS hR hX hM
    letI := partCoefficients hS hR hX hM
    (inferInstance : Module ℂ X) = MX ∧
      (inferInstance : Module ℂ M) = MM ∧
      (inferInstance : Module ℂ (Tensor R X M)) = MT ∧
      (inferInstance : NonUnitalModule S (Tensor R X M)) = HS ∧
      (inferInstance : NonUnitalModule Rᵐᵒᵖ DM) = NonUnitalModuleDual.dualAction hR hM ∧
      (inferInstance : NonUnitalModule Sᵐᵒᵖ F) = fullAction (M := M) hS hX hSX ∧
      (inferInstance : NonUnitalModule Sᵐᵒᵖ DT) = dualAction (M := M) hS hX hSX ∧
      (inferInstance : NonUnitalModule Sᵐᵒᵖ H) = homAction hR hX hM ∧
      (inferInstance : Module ℂ HP) = partCoefficients hS hR hX hM :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable (hc : NonUnitalBimoduleTensorScalars.InputCompatible ℂ (S := S) hR hRX)

/-- The factor and tensor scalar formulas retain MX, MM and MT under competitors. -/
example (c : ℂ) (x : X) (m : M) :
    letI := MX
    letI := MM
    letI := MT
    c • tmul R X M x m = tmul R X M (c • x) m ∧
      c • tmul R X M x m = tmul R X M x (c • m) :=
  ⟨NondegenerateTensorScalars.smul_tmul_left ℂ R X M hR hRX hM c x m,
    NondegenerateTensorScalars.smul_tmul_right ℂ R X M hR hM c x m⟩

/-- All three coefficient identifications are the proved equalities on the named actions. -/
example :
    letI := HS
    letI := NonUnitalModuleDual.dualAction hR hM
    letI := homAction hR hX hM
    letI := partAction hS hR hX hM
    NondegenerateScalars.module ℂ hS
        (NondegenerateTensorFunctor.isNondegenerate hS hX hSX M) = MT ∧
      NondegenerateScalars.module ℂ hR.op
        (NonUnitalModuleDual.isNondegenerate hR hM) =
        NonUnitalModuleDual.dualModule hR hM ∧
      NondegenerateScalars.module ℂ hS.op
        (nondegeneratePart_isNondegenerate (M := H) hS.op) =
        partCoefficients hS hR hX hM :=
  ⟨tensorModule_eq hS hR hX hSX hRX hM hc,
    targetRecoveredCoefficients_eq hR hM,
    partRecoveredCoefficients_eq hS hR hX hRX hM hc⟩

/-- Ambient original-action laws still use fullAction and the exact rightSourceAction. -/
example (a : Sᵐᵒᵖ) (ell : F) (h : H) :
    letI := fullAction (M := M) hS hX hSX
    letI := homAction hR hX hM
    curry hS hR hX hSX hRX hM hc (a • ell) =
        a • curry hS hR hX hSX hRX hM hc ell ∧
      uncurry hS hR hX hSX hRX hM hc (a • h) =
        a • uncurry hS hR hX hSX hRX hM hc h :=
  ⟨curry_action hS hR hX hSX hRX hM hc a ell,
    uncurry_action hS hR hX hSX hRX hM hc a h⟩

/-- Restricted scalar formulas use the named part Modules after the original inclusions. -/
example (c : ℂ) (ell : DT) (h : HP) (x : X) (m : M) :
    letI := dualCoefficients (M := M) hS hX hSX
    letI := partCoefficients hS hR hX hM
    ((curryPart hS hR hX hSX hRX hM hc (c • ell)).val x).val m =
        c • ell.val (tmul R X M x m) ∧
      (uncurryPart hS hR hX hSX hRX hM hc (c • h)).val (tmul R X M x m) =
        c • (h.val x).val m :=
  ⟨curryPart_smul_apply hS hR hX hSX hRX hM hc c ell x m,
    uncurryPart_smul_tmul hS hR hX hSX hRX hM hc c h x m⟩

/-- The linear and original-action refinements keep their entire additive maps. -/
example :
    letI := dualAction (M := M) hS hX hSX
    letI := partAction hS hR hX hM
    (curryPartLinear hS hR hX hSX hRX hM hc).toAddMonoidHom =
        (curryPartHom hS hR hX hSX hRX hM hc).toAddMonoidHom ∧
      (uncurryPartLinear hS hR hX hSX hRX hM hc).toAddMonoidHom =
        (uncurryPartHom hS hR hX hSX hRX hM hc).toAddMonoidHom := by
  let := dualAction (M := M) hS hX hSX
  let := partAction hS hR hX hM
  exact ⟨curryPartLinear_toAddMonoidHom hS hR hX hSX hRX hM hc,
    uncurryPartLinear_toAddMonoidHom hS hR hX hSX hRX hM hc⟩

end CompetingStructures

section CompetingOriginalActions

variable {S : Type uS} {R : Type uR} {X : Type uX} {M : Type uM}
  [NonUnitalRing S] [NonUnitalRing R]
  [Module ℂ S] [IsScalarTower ℂ S S] [SMulCommClass ℂ S S]
  [Module ℂ R] [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
  [AddCommGroup X] [sx : NonUnitalModule S X] [rx : NonUnitalModule Rᵐᵒᵖ X]
  [AddCommGroup M] [rm : NonUnitalModule R M]
  (hS : IsIdempotented S) (hR : IsIdempotented R)
  (hX : ActionsCommute S R X) (hSX : IsNondegenerate S X)
  (hRX : IsNondegenerate Rᵐᵒᵖ X) (hM : IsNondegenerate R M)
  (hc : NonUnitalBimoduleTensorScalars.InputCompatible ℂ (S := S) hR hRX)
  [otherSX : NonUnitalModule S X] [otherRX : NonUnitalModule Rᵐᵒᵖ X]
  [otherRM : NonUnitalModule R M]

set_option linter.overlappingInstances false in
/-- Reselecting the original factor actions also selects the actual balanced tensor. -/
example :
    letI := sx
    letI := rx
    letI := rm
    letI := NonUnitalBimoduleTensor.leftModule hX M
    letI := NonUnitalModuleDual.dualAction hR hM
    ∀ (ell : FullDual (M := M) hS hX hSX) (h : Hom (X := X) hR hM) (x : X) (m : M),
      (curry hS hR hX hSX hRX hM hc ell x).val m = ell (tmul R X M x m) ∧
        uncurry hS hR hX hSX hRX hM hc h (tmul R X M x m) = (h x).val m := by
  let := sx
  let := rx
  let := rm
  intro ell h x m
  exact ⟨curry_apply hS hR hX hSX hRX hM hc ell x m,
    uncurry_tmul hS hR hX hSX hRX hM hc h x m⟩

set_option linter.overlappingInstances false in
/-- The restricted functions still refer to the original selected actions and inclusions. -/
example :
    letI := sx
    letI := rx
    letI := rm
    letI := dualAction (M := M) hS hX hSX
    letI := partAction hS hR hX hM
    ∀ (ell : Dual (M := M) hS hX hSX) (h : HomPart hS hR hX hM)
      (a : Sᵐᵒᵖ) (x : X) (m : M),
      ((curryPartHom hS hR hX hSX hRX hM hc (a • ell)).val x).val m =
          ell.val (tmul R X M (a.unop • x) m) ∧
        (uncurryPartHom hS hR hX hSX hRX hM hc (a • h)).val (tmul R X M x m) =
          (h.val (a.unop • x)).val m := by
  let := sx
  let := rx
  let := rm
  intro ell h a x m
  exact ⟨rfl, rfl⟩

end CompetingOriginalActions

section Boundary

variable {S : Type uS} {R : Type uR} {X : Type uX} {M : Type uM}
  [NonUnitalRing S] [NonUnitalRing R]
  [Module ℂ S] [IsScalarTower ℂ S S] [SMulCommClass ℂ S S]
  [Module ℂ R] [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
  [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
  [AddCommGroup M] [NonUnitalModule R M]
  (hS : IsIdempotented S) (hR : IsIdempotented R)
  (hX : ActionsCommute S R X) (hSX : IsNondegenerate S X)
  (hRX : IsNondegenerate Rᵐᵒᵖ X) (hM : IsNondegenerate R M)
  (hc : NonUnitalBimoduleTensorScalars.InputCompatible ℂ (S := S) hR hRX)

local notation "C" => curry hS hR hX hSX hRX hM hc
local notation "U" => uncurry hS hR hX hSX hRX hM hc

/-- Both actual ambient and restricted constructions preserve zero. -/
example :
    C 0 = 0 ∧ U 0 = 0 ∧
      curryPart hS hR hX hSX hRX hM hc 0 = 0 ∧
      uncurryPart hS hR hX hSX hRX hM hc 0 = 0 :=
  ⟨(curryAdd hS hR hX hSX hRX hM hc).map_zero,
    (uncurryAddMap hS hR hX hSX hRX hM hc).map_zero,
    (curryPartHom hS hR hX hSX hRX hM hc).map_zero,
    (uncurryPartHom hS hR hX hSX hRX hM hc).map_zero⟩

/-- A subsingleton original X makes every functional and intertwiner zero. -/
example [Subsingleton X] (ell : FullDual (M := M) hS hX hSX) (h : Hom (X := X) hR hM) :
    C ell = 0 ∧ U h = 0 := by
  let := NonUnitalBimoduleTensor.leftModule hX M
  let := NondegenerateScalars.module ℂ hS
    (NondegenerateTensorFunctor.isNondegenerate hS hX hSX M)
  have he : ell = 0 := by
    apply full_ext hS hX hSX
    intro x m
    rw [Subsingleton.elim x 0, NonUnitalModuleTensor.zero_tmul]
    exact ell.map_zero
  have hh : h = 0 := NonUnitalModuleHom.ext fun x => by
    rw [Subsingleton.elim x 0, h.map_zero]
    rfl
  exact ⟨he ▸ (curryAdd hS hR hX hSX hRX hM hc).map_zero,
    hh ▸ (uncurryAddMap hS hR hX hSX hRX hM hc).map_zero⟩

/-- The same conclusion holds when the other original tensor factor is subsingleton. -/
example [Subsingleton M] (ell : FullDual (M := M) hS hX hSX) (h : Hom (X := X) hR hM) :
    C ell = 0 ∧ U h = 0 := by
  let := NonUnitalBimoduleTensor.leftModule hX M
  let := NondegenerateScalars.module ℂ hS
    (NondegenerateTensorFunctor.isNondegenerate hS hX hSX M)
  have he : ell = 0 := by
    apply full_ext hS hX hSX
    intro x m
    rw [Subsingleton.elim m 0, NonUnitalModuleTensor.tmul_zero]
    exact ell.map_zero
  have hh : h = 0 := by
    apply NonUnitalModuleHom.ext
    intro x
    apply Subtype.ext
    let := NondegenerateScalars.module ℂ hR hM
    apply LinearMap.ext
    intro m
    rw [Subsingleton.elim m 0]
    exact (h x).val.map_zero
  exact ⟨he ▸ (curryAdd hS hR hX hSX hRX hM hc).map_zero,
    hh ▸ (uncurryAddMap hS hR hX hSX hRX hM hc).map_zero⟩

end Boundary

section RegularComplex

local instance : NonUnitalModule ℂ ℂ := NonUnitalModule.regular ℂ
local instance : NonUnitalModule ℂᵐᵒᵖ ℂ := NonUnitalModule.rightRegular ℂ

private theorem complexIdempotented : IsIdempotented ℂ := IsIdempotented.of_ring ℂ

private theorem complexLeftNondegenerate : IsNondegenerate ℂ ℂ :=
  NondegenerateTensorFunctor.regular_isNondegenerate complexIdempotented

private theorem complexRightNondegenerate : IsNondegenerate ℂᵐᵒᵖ ℂ :=
  NondegenerateTensorFunctor.rightRegular_isNondegenerate complexIdempotented

private theorem complexLeftScalar (c m : ℂ) :
    NondegenerateScalars.scalarMul ℂ complexLeftNondegenerate c m = c * m := by
  have he : ((⟨1, IsIdempotentElem.one⟩ : Idempotent ℂ) : ℂ) • m = m := one_mul m
  have hh := NondegenerateScalars.scalarMul_eq ℂ complexIdempotented
    complexLeftNondegenerate c m ⟨1, IsIdempotentElem.one⟩ he
  change NondegenerateScalars.scalarMul ℂ complexLeftNondegenerate c m = (c * 1) * m at hh
  simpa only [mul_one] using hh

private theorem complexRightScalar (c x : ℂ) :
    NondegenerateScalars.scalarMul ℂ complexRightNondegenerate c x = x * c := by
  have he : ((⟨op 1, IsIdempotentElem.one⟩ : Idempotent ℂᵐᵒᵖ) : ℂᵐᵒᵖ) • x = x :=
    mul_one x
  have hh := NondegenerateScalars.scalarMul_eq ℂ complexIdempotented.op
    complexRightNondegenerate c x ⟨op 1, IsIdempotentElem.one⟩ he
  change NondegenerateScalars.scalarMul ℂ complexRightNondegenerate c x = x * (c * 1) at hh
  simpa only [mul_one] using hh

private theorem complexCompatible :
    NonUnitalBimoduleTensorScalars.InputCompatible ℂ (S := ℂ)
      complexIdempotented complexRightNondegenerate := by
  apply (NonUnitalBimoduleTensorScalars.inputCompatible_iff ℂ (S := ℂ)
    complexIdempotented complexRightNondegenerate).2
  intro c s x
  change (c * s) * x =
    NondegenerateScalars.scalarMul ℂ complexRightNondegenerate c (s * x)
  rw [complexRightScalar]
  ring

private def complexFunctional (x : ℂ) :
    NonUnitalModuleDual.FullDual complexIdempotented complexLeftNondegenerate :=
  @LinearMap.mk ℂ ℂ _ _ (RingHom.id ℂ) ℂ ℂ _ _
    (NondegenerateScalars.module ℂ complexIdempotented complexLeftNondegenerate)
    (inferInstance : Module ℂ ℂ) ⟨(x * ·), mul_add x⟩ (by
    intro c m
    change x * NondegenerateScalars.scalarMul ℂ complexLeftNondegenerate c m = c * (x * m)
    rw [complexLeftScalar]
    ring)

private def complexDual (x : ℂ) :
    NonUnitalModuleDual.Dual complexIdempotented complexLeftNondegenerate := by
  refine ⟨complexFunctional x, ?_⟩
  exact (NonUnitalModuleDual.mem_dual_iff complexIdempotented complexLeftNondegenerate _).2
    ⟨⟨1, IsIdempotentElem.one⟩, fun m => by
      change x * (1 * m) = x * m
      rw [one_mul]⟩

private def complexHom : Hom (X := ℂ) complexIdempotented complexLeftNondegenerate where
  toFun := complexDual
  map_zero' := by
    apply Subtype.ext
    apply DFunLike.ext
    intro m
    exact zero_mul m
  map_add' x y := by
    apply Subtype.ext
    apply DFunLike.ext
    intro m
    exact add_mul x y m
  map_smul' r x := by
    apply Subtype.ext
    apply DFunLike.ext
    intro m
    exact mul_assoc x (unop r) m

local notation "hC" => complexIdempotented
local notation "hL" => complexLeftNondegenerate
local notation "hR" => complexRightNondegenerate
local notation "hX" => NonUnitalModule.regular_actionsCommute ℂ
local notation "hc" => complexCompatible

/-- The actual quotient lift of multiplication for the original regular complex actions. -/
def regularComplexTensorFunctional : FullDual (M := ℂ) hC hX hL :=
  uncurry hC hC hX hL hR hL hc complexHom

/-- Both actual ambient maps evaluate multiplication on the original balanced pure tensor. -/
example (x m : ℂ) :
    regularComplexTensorFunctional (tmul ℂ ℂ ℂ x m) = x * m ∧
      (curry hC hC hX hL hR hL hc regularComplexTensorFunctional x).val m = x * m :=
  ⟨rfl, rfl⟩

private def complexHomPart : HomPart hC hC hX hL := by
  refine ⟨complexHom, ⟨⟨op 1, IsIdempotentElem.one⟩, ?_⟩⟩
  apply NonUnitalModuleHom.ext
  intro x
  change complexDual (1 * x) = complexDual x
  rw [one_mul]

private def complexTensorDual : Dual (M := ℂ) hC hX hL :=
  uncurryPart hC hC hX hL hR hL hc complexHomPart

/-- The actual tensor-dual inclusion retains the entire quotient-lift functional. -/
example : complexTensorDual.val = regularComplexTensorFunctional := rfl

/-- Both restricted directions retain literal evaluation on original pure tensors. -/
example (x m : ℂ) :
    ((curryPart hC hC hX hL hR hL hc complexTensorDual).val x).val m = x * m ∧
      (uncurryPart hC hC hX hL hR hL hc complexHomPart).val (tmul ℂ ℂ ℂ x m) = x * m :=
  ⟨rfl, rfl⟩

/-- The original pure tensor at 2 and 3 is detected with value 6 in both directions. -/
example :
    regularComplexTensorFunctional (tmul ℂ ℂ ℂ 2 3) = 6 ∧
      ((curryPart hC hC hX hL hR hL hc complexTensorDual).val 2).val 3 = 6 ∧
      (uncurryPart hC hC hX hL hR hL hc complexHomPart).val (tmul ℂ ℂ ℂ 2 3) = 6 := by
  change (2 : ℂ) * 3 = 6 ∧ (2 : ℂ) * 3 = 6 ∧ (2 : ℂ) * 3 = 6
  norm_num

/-- Nonzero evaluation proves that this is a nonzero original balanced tensor. -/
example : tmul ℂ ℂ ℂ (2 : ℂ) 3 ≠ 0 := by
  let := NonUnitalBimoduleTensor.leftModule hX ℂ
  let := NondegenerateScalars.module ℂ hC
    (NondegenerateTensorFunctor.isNondegenerate hC hX hL ℂ)
  intro h
  have hv := congrArg regularComplexTensorFunctional h
  change (2 : ℂ) * 3 = regularComplexTensorFunctional 0 at hv
  rw [regularComplexTensorFunctional.map_zero] at hv
  norm_num at hv

/-- The constructed full functional and its actual tensor-dual restriction are nonzero. -/
example : regularComplexTensorFunctional ≠ 0 ∧ complexTensorDual ≠ 0 := by
  have hf : regularComplexTensorFunctional ≠ 0 := by
    intro h
    have hv := congrArg (fun ell : FullDual (M := ℂ) hC hX hL =>
      ell (tmul ℂ ℂ ℂ 2 3)) h
    change (2 : ℂ) * 3 = 0 at hv
    norm_num at hv
  exact ⟨hf, fun h => hf (congrArg Subtype.val h)⟩

/-- Evaluation also detects the constructed Hom part and the actual restricted curry. -/
example :
    complexHomPart ≠ 0 ∧ curryPart hC hC hX hL hR hL hc complexTensorDual ≠ 0 := by
  constructor
  · intro h
    have hv := congrArg (fun k : HomPart hC hC hX hL => (k.val 2).val 3) h
    change (2 : ℂ) * 3 = 0 at hv
    norm_num at hv
  · intro h
    have hv := congrArg (fun k : HomPart hC hC hX hL => (k.val 2).val 3) h
    change (2 : ℂ) * 3 = 0 at hv
    norm_num at hv

end RegularComplex

end Langlands.Algebra.NonUnitalTensorDualMapsChecks
