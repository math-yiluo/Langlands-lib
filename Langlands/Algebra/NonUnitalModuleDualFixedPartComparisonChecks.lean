import Langlands.Algebra.NonUnitalModuleDualFixedPartComparison
import Mathlib.Algebra.Module.PUnit
import Mathlib.Algebra.Ring.PUnit

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDualFixedPartComparisonChecks

open MulOpposite
open NonUnitalModuleCorner (FixedPart)
open NonUnitalModuleDualFixedPartMaps
open NonUnitalModuleDualFixedPartComparison

universe uA uM

/-! Complete unapplied interfaces at algebra universe 0, carrier universe 1. -/

example : {A : Type 0} → [NonUnitalRing A] → (e : Idempotent A) →
    (Idempotent.Corner e)ᵐᵒᵖ ≃+* Idempotent.Corner (oppositeIdempotent e) :=
  @cornerOppositeEquiv.{0}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    Type 1 :=
  @FullRightFixedPart.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    Module ℂ (FullRightFixedPart hA hM e) :=
  @fullRightFixedModule.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    letI := NonUnitalModuleCorner.complexModule hA hM e
    Module (Idempotent.Corner (oppositeIdempotent e))
      (Module.Dual ℂ (FixedPart e M)) :=
  @fixedPartDualCornerModule.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    letI := rightFixedModule hA hM e
    letI := fullRightFixedModule hA hM e
    RightFixedPart hA hM e →ₗ[ℂ] FullRightFixedPart hA hM e :=
  @toFullFixed.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    letI := rightFixedModule hA hM e
    letI := fullRightFixedModule hA hM e
    FullRightFixedPart hA hM e →ₗ[ℂ] RightFixedPart hA hM e :=
  @fromFullFixed.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    RightFixedPart hA hM e →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      FullRightFixedPart hA hM e :=
  @toFullFixedCorner.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    FullRightFixedPart hA hM e →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      RightFixedPart hA hM e :=
  @fromFullFixedCorner.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    RightFixedPart hA hM e →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      Module.Dual ℂ (FixedPart e M) :=
  @restrictionCorner.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    Module.Dual ℂ (FixedPart e M) →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      RightFixedPart hA hM e :=
  @extensionCorner.{0, 1}

/-! Complete unapplied interfaces at algebra universe 1, carrier universe 0. -/

example : {A : Type 1} → [NonUnitalRing A] → (e : Idempotent A) →
    (Idempotent.Corner e)ᵐᵒᵖ ≃+* Idempotent.Corner (oppositeIdempotent e) :=
  @cornerOppositeEquiv.{1}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    Type 0 :=
  @FullRightFixedPart.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    Module ℂ (FullRightFixedPart hA hM e) :=
  @fullRightFixedModule.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    letI := NonUnitalModuleCorner.complexModule hA hM e
    Module (Idempotent.Corner (oppositeIdempotent e))
      (Module.Dual ℂ (FixedPart e M)) :=
  @fixedPartDualCornerModule.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    letI := rightFixedModule hA hM e
    letI := fullRightFixedModule hA hM e
    RightFixedPart hA hM e →ₗ[ℂ] FullRightFixedPart hA hM e :=
  @toFullFixed.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    letI := rightFixedModule hA hM e
    letI := fullRightFixedModule hA hM e
    FullRightFixedPart hA hM e →ₗ[ℂ] RightFixedPart hA hM e :=
  @fromFullFixed.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    RightFixedPart hA hM e →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      FullRightFixedPart hA hM e :=
  @toFullFixedCorner.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    FullRightFixedPart hA hM e →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      RightFixedPart hA hM e :=
  @fromFullFixedCorner.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    RightFixedPart hA hM e →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      Module.Dual ℂ (FixedPart e M) :=
  @restrictionCorner.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (e : Idempotent A) →
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    Module.Dual ℂ (FixedPart e M) →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      RightFixedPart hA hM e :=
  @extensionCorner.{1, 0}

section CanonicalScalars

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M)

/-- Freeze the ordinary pointwise complex module on the precise full dual. -/
@[instance_reducible]
private def fullComplexModule : Module ℂ (NonUnitalModuleDual.FullDual hA hM) := by
  letI := NondegenerateScalars.complexModule hA hM
  exact inferInstance

section CompetingAmbientComplex

variable [competingAmbient : Module ℂ M]

example (e : Idempotent A) :
    FullRightFixedPart hA hM e =
      @FixedPart Aᵐᵒᵖ _ (oppositeIdempotent e)
        (NonUnitalModuleDual.FullDual hA hM) _ (NonUnitalModuleDual.fullAction hA hM) := rfl

example (e : Idempotent A) :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    ∀ (a : Idempotent.Corner (oppositeIdempotent e))
      (ell : Module.Dual ℂ (FixedPart e M)),
      a • ell = ell.comp
        (NonUnitalModuleCorner.cornerLinearAction hA hM e (cornerUnop e a)) :=
  fixedPartDualCornerModule_functional hA hM e

example (e : Idempotent A) (phi : RightFixedPart hA hM e) :
    letI := NondegenerateScalars.complexModule hA hM
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    restrictionCorner hA hM e phi =
      phi.val.val.comp (NonUnitalModuleCorner.inclusionLinear hA hM e) :=
  restrictionCorner_functional hA hM e phi

example (e : Idempotent A) :
    letI := NondegenerateScalars.complexModule hA hM
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    ∀ ell : Module.Dual ℂ (FixedPart e M),
      (extensionCorner hA hM e ell).val.val =
        ell.comp (NonUnitalModuleCorner.projectionLinear hA hM e) :=
  extensionCorner_functional hA hM e

end CompetingAmbientComplex

section CompetingDualActions

variable [competingFull : NonUnitalModule Aᵐᵒᵖ (NonUnitalModuleDual.FullDual hA hM)]
  [competingDual : NonUnitalModule Aᵐᵒᵖ (NonUnitalModuleDual.Dual hA hM)]

example (e : Idempotent A) :
    FullRightFixedPart hA hM e =
      @FixedPart Aᵐᵒᵖ _ (oppositeIdempotent e)
        (NonUnitalModuleDual.FullDual hA hM) _ (NonUnitalModuleDual.fullAction hA hM) := rfl

example (e : Idempotent A) :
    RightFixedPart hA hM e =
      @FixedPart Aᵐᵒᵖ _ (oppositeIdempotent e)
        (NonUnitalModuleDual.Dual hA hM) _ (NonUnitalModuleDual.dualAction hA hM) := rfl

example (e : Idempotent A) :
    letI : Module (Idempotent.Corner (oppositeIdempotent e)) (RightFixedPart hA hM e) :=
      @NonUnitalModuleCorner.fixedPartModule Aᵐᵒᵖ _ (oppositeIdempotent e)
        (NonUnitalModuleDual.Dual hA hM) _ (NonUnitalModuleDual.dualAction hA hM)
    letI : Module (Idempotent.Corner (oppositeIdempotent e)) (FullRightFixedPart hA hM e) :=
      @NonUnitalModuleCorner.fixedPartModule Aᵐᵒᵖ _ (oppositeIdempotent e)
        (NonUnitalModuleDual.FullDual hA hM) _ (NonUnitalModuleDual.fullAction hA hM)
    RightFixedPart hA hM e →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      FullRightFixedPart hA hM e := toFullFixedCorner hA hM e

example (e : Idempotent A) :
    letI : Module (Idempotent.Corner (oppositeIdempotent e)) (RightFixedPart hA hM e) :=
      @NonUnitalModuleCorner.fixedPartModule Aᵐᵒᵖ _ (oppositeIdempotent e)
        (NonUnitalModuleDual.Dual hA hM) _ (NonUnitalModuleDual.dualAction hA hM)
    letI : Module (Idempotent.Corner (oppositeIdempotent e)) (FullRightFixedPart hA hM e) :=
      @NonUnitalModuleCorner.fixedPartModule Aᵐᵒᵖ _ (oppositeIdempotent e)
        (NonUnitalModuleDual.FullDual hA hM) _ (NonUnitalModuleDual.fullAction hA hM)
    FullRightFixedPart hA hM e →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      RightFixedPart hA hM e := fromFullFixedCorner hA hM e

end CompetingDualActions

section CompetingFixedScalars

variable (e : Idempotent A)
  [competingFixed : Module ℂ (FixedPart e M)]
  [competingRight : Module ℂ (RightFixedPart hA hM e)]
  [competingFull : Module ℂ (FullRightFixedPart hA hM e)]
  [competingFullDual : Module ℂ (NonUnitalModuleDual.FullDual hA hM)]
  [competingDual : Module ℂ (NonUnitalModuleDual.Dual hA hM)]

example :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    Module (Idempotent.Corner (oppositeIdempotent e))
      (Module.Dual ℂ (FixedPart e M)) := fixedPartDualCornerModule hA hM e

example :
    letI := rightFixedModule hA hM e
    letI := fullRightFixedModule hA hM e
    RightFixedPart hA hM e →ₗ[ℂ] FullRightFixedPart hA hM e := toFullFixed hA hM e

example :
    letI := rightFixedModule hA hM e
    letI := fullRightFixedModule hA hM e
    FullRightFixedPart hA hM e →ₗ[ℂ] RightFixedPart hA hM e := fromFullFixed hA hM e

example (c : ℂ) (psi : FullRightFixedPart hA hM e) :
    ((fullRightFixedModule hA hM e).toSMul.smul c psi).val =
      (fullComplexModule hA hM).toSMul.smul c psi.val := rfl

example (c : ℂ) (phi : RightFixedPart hA hM e) :
    ((rightFixedModule hA hM e).toSMul.smul c phi).val.val =
      (fullComplexModule hA hM).toSMul.smul c phi.val.val := rfl

example :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    letI := rightFixedModule hA hM e
    (restrictionCorner hA hM e).toAddMonoidHom =
      (restriction hA hM e).toAddMonoidHom := restrictionCorner_toAddMonoidHom hA hM e

example :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    letI := rightFixedModule hA hM e
    (extensionCorner hA hM e).toAddMonoidHom =
      (extension hA hM e).toAddMonoidHom := extensionCorner_toAddMonoidHom hA hM e

end CompetingFixedScalars

section CompetingOriginalCorner

variable (e : Idempotent A)
  [competingCorner : Module (Idempotent.Corner e) (FixedPart e M)]

example :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := NonUnitalModuleCorner.fixedPartModule e M
    letI := fixedPartDualCornerModule hA hM e
    ∀ (a : Idempotent.Corner (oppositeIdempotent e))
      (ell : Module.Dual ℂ (FixedPart e M)) (x : FixedPart e M),
      (a • ell) x = ell ((cornerUnop e a) • x) :=
  fixedPartDualCornerModule_apply hA hM e

example :
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := NonUnitalModuleCorner.fixedPartModule e M
    letI := fixedPartDualCornerModule hA hM e
    SMulCommClass ℂ (Idempotent.Corner (oppositeIdempotent e))
      (Module.Dual ℂ (FixedPart e M)) :=
  fixedPartDualCornerModule_smulCommClass hA hM e

end CompetingOriginalCorner

section CompetingFixedCorners

variable (e : Idempotent A)
  [competingRightCorner : Module (Idempotent.Corner (oppositeIdempotent e))
    (RightFixedPart hA hM e)]
  [competingFullCorner : Module (Idempotent.Corner (oppositeIdempotent e))
    (FullRightFixedPart hA hM e)]

example :
    letI : Module (Idempotent.Corner (oppositeIdempotent e)) (RightFixedPart hA hM e) :=
      @NonUnitalModuleCorner.fixedPartModule Aᵐᵒᵖ _ (oppositeIdempotent e)
        (NonUnitalModuleDual.Dual hA hM) _ (NonUnitalModuleDual.dualAction hA hM)
    letI : Module (Idempotent.Corner (oppositeIdempotent e)) (FullRightFixedPart hA hM e) :=
      @NonUnitalModuleCorner.fixedPartModule Aᵐᵒᵖ _ (oppositeIdempotent e)
        (NonUnitalModuleDual.FullDual hA hM) _ (NonUnitalModuleDual.fullAction hA hM)
    RightFixedPart hA hM e →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      FullRightFixedPart hA hM e := toFullFixedCorner hA hM e

example :
    letI : Module (Idempotent.Corner (oppositeIdempotent e)) (RightFixedPart hA hM e) :=
      @NonUnitalModuleCorner.fixedPartModule Aᵐᵒᵖ _ (oppositeIdempotent e)
        (NonUnitalModuleDual.Dual hA hM) _ (NonUnitalModuleDual.dualAction hA hM)
    letI : Module (Idempotent.Corner (oppositeIdempotent e)) (FullRightFixedPart hA hM e) :=
      @NonUnitalModuleCorner.fixedPartModule Aᵐᵒᵖ _ (oppositeIdempotent e)
        (NonUnitalModuleDual.FullDual hA hM) _ (NonUnitalModuleDual.fullAction hA hM)
    FullRightFixedPart hA hM e →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      RightFixedPart hA hM e := fromFullFixedCorner hA hM e

example :
    letI := fullRightFixedModule hA hM e
    letI : Module (Idempotent.Corner (oppositeIdempotent e)) (FullRightFixedPart hA hM e) :=
      @NonUnitalModuleCorner.fixedPartModule Aᵐᵒᵖ _ (oppositeIdempotent e)
        (NonUnitalModuleDual.FullDual hA hM) _ (NonUnitalModuleDual.fullAction hA hM)
    SMulCommClass ℂ (Idempotent.Corner (oppositeIdempotent e))
      (FullRightFixedPart hA hM e) := fullRightFixedModule_smulCommClass hA hM e

example :
    letI : Module (Idempotent.Corner (oppositeIdempotent e)) (RightFixedPart hA hM e) :=
      @NonUnitalModuleCorner.fixedPartModule Aᵐᵒᵖ _ (oppositeIdempotent e)
        (NonUnitalModuleDual.Dual hA hM) _ (NonUnitalModuleDual.dualAction hA hM)
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    RightFixedPart hA hM e →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      Module.Dual ℂ (FixedPart e M) := restrictionCorner hA hM e

example :
    letI : Module (Idempotent.Corner (oppositeIdempotent e)) (RightFixedPart hA hM e) :=
      @NonUnitalModuleCorner.fixedPartModule Aᵐᵒᵖ _ (oppositeIdempotent e)
        (NonUnitalModuleDual.Dual hA hM) _ (NonUnitalModuleDual.dualAction hA hM)
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    Module.Dual ℂ (FixedPart e M) →ₗ[Idempotent.Corner (oppositeIdempotent e)]
      RightFixedPart hA hM e := extensionCorner hA hM e

end CompetingFixedCorners

end CanonicalScalars

/-- The zero fixed subgroup is a singleton for every original nonunital action. -/
private theorem fixedPartZero_subsingleton {A : Type uA} [NonUnitalRing A]
    {M : Type uM} [AddCommGroup M] [NonUnitalModule A M] :
    Subsingleton (FixedPart (⟨0, IsIdempotentElem.zero⟩ : Idempotent A) M) := by
  refine ⟨fun x y => Subtype.ext ?_⟩
  have hx : (0 : A) • x.val = x.val := x.property
  have hy : (0 : A) • y.val = y.val := y.property
  rw [NonUnitalModule.zero_smul] at hx hy
  exact hx.symm.trans hy

section ZeroIdempotent

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M)

example :
    let e : Idempotent A := ⟨0, IsIdempotentElem.zero⟩
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    letI := rightFixedModule hA hM e
    letI := fullRightFixedModule hA hM e
    toFullFixed hA hM e = 0 ∧ fromFullFixed hA hM e = 0 ∧
      toFullFixedCorner hA hM e = 0 ∧ fromFullFixedCorner hA hM e = 0 ∧
      restrictionCorner hA hM e = 0 ∧ extensionCorner hA hM e = 0 := by
  let e : Idempotent A := ⟨0, IsIdempotentElem.zero⟩
  let := NonUnitalModuleCorner.complexModule hA hM e
  let := fixedPartDualCornerModule hA hM e
  let := rightFixedModule hA hM e
  let := fullRightFixedModule hA hM e
  let : NonUnitalModule Aᵐᵒᵖ (NonUnitalModuleDual.FullDual hA hM) :=
    NonUnitalModuleDual.fullAction hA hM
  let : NonUnitalModule Aᵐᵒᵖ (NonUnitalModuleDual.Dual hA hM) :=
    NonUnitalModuleDual.dualAction hA hM
  let : Subsingleton (FixedPart e M) := fixedPartZero_subsingleton
  let : Subsingleton (RightFixedPart hA hM e) := fixedPartZero_subsingleton
  let : Subsingleton (FullRightFixedPart hA hM e) := fixedPartZero_subsingleton
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _,
    Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

end ZeroIdempotent

/-- Every original action on a singleton group is nondegenerate using zero. -/
private theorem subsingleton_nondegenerate {A : Type uA} [NonUnitalRing A]
    {M : Type uM} [AddCommGroup M] [NonUnitalModule A M] [Subsingleton M] :
    IsNondegenerate A M :=
  fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩

section ZeroModule

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  (hA : IsIdempotented A)

example (e : Idempotent A) :
    letI : NonUnitalModule A PUnit.{uM + 1} := NonUnitalModule.zero
    let hM := subsingleton_nondegenerate (A := A) (M := PUnit.{uM + 1})
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    letI := rightFixedModule hA hM e
    letI := fullRightFixedModule hA hM e
    (toFullFixedCorner hA hM e).toAddMonoidHom =
        (toFullFixed hA hM e).toAddMonoidHom ∧
      (fromFullFixedCorner hA hM e).toAddMonoidHom =
        (fromFullFixed hA hM e).toAddMonoidHom ∧
      (restrictionCorner hA hM e).toAddMonoidHom =
        (restriction hA hM e).toAddMonoidHom ∧
      (extensionCorner hA hM e).toAddMonoidHom =
        (extension hA hM e).toAddMonoidHom := by
  let : NonUnitalModule A PUnit.{uM + 1} := NonUnitalModule.zero
  let hM := subsingleton_nondegenerate (A := A) (M := PUnit.{uM + 1})
  exact ⟨toFullFixedCorner_toAddMonoidHom hA hM e,
    fromFullFixedCorner_toAddMonoidHom hA hM e,
    restrictionCorner_toAddMonoidHom hA hM e,
    extensionCorner_toAddMonoidHom hA hM e⟩

end ZeroModule

section ZeroAlgebra

example (e : Idempotent PUnit.{uA + 1}) :
    letI : NonUnitalModule PUnit.{uA + 1} PUnit.{uM + 1} := NonUnitalModule.zero
    let hA := IsIdempotented.of_ring PUnit.{uA + 1}
    let hM := subsingleton_nondegenerate
      (A := PUnit.{uA + 1}) (M := PUnit.{uM + 1})
    letI := NonUnitalModuleCorner.complexModule hA hM e
    letI := fixedPartDualCornerModule hA hM e
    letI := rightFixedModule hA hM e
    letI := fullRightFixedModule hA hM e
    (toFullFixedCorner hA hM e).toAddMonoidHom =
        (toFullFixed hA hM e).toAddMonoidHom ∧
      (fromFullFixedCorner hA hM e).toAddMonoidHom =
        (fromFullFixed hA hM e).toAddMonoidHom ∧
      (restrictionCorner hA hM e).toAddMonoidHom =
        (restriction hA hM e).toAddMonoidHom ∧
      (extensionCorner hA hM e).toAddMonoidHom =
        (extension hA hM e).toAddMonoidHom := by
  let : NonUnitalModule PUnit.{uA + 1} PUnit.{uM + 1} := NonUnitalModule.zero
  let hA := IsIdempotented.of_ring PUnit.{uA + 1}
  let hM := subsingleton_nondegenerate
    (A := PUnit.{uA + 1}) (M := PUnit.{uM + 1})
  exact ⟨toFullFixedCorner_toAddMonoidHom hA hM e,
    fromFullFixedCorner_toAddMonoidHom hA hM e,
    restrictionCorner_toAddMonoidHom hA hM e,
    extensionCorner_toAddMonoidHom hA hM e⟩

end ZeroAlgebra

end Langlands.Algebra.NonUnitalModuleDualFixedPartComparisonChecks
