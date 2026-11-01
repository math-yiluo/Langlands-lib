import Langlands.Algebra.NonUnitalModuleDualFixedPartComparison
import Langlands.Algebra.NonUnitalModuleDualMap

/-!
Statements for the actual full-fixed and right-corner comparisons in
Renard I.4.1, using the published construction and original actions.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDualFixedPartComparisonStatements

open NonUnitalModuleCorner (FixedPart)
open NonUnitalModuleDualFixedPartMaps
open NonUnitalModuleDualFixedPartComparison

universe uA uM uN

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M)

local instance : NonUnitalModule Aᵐᵒᵖ (NonUnitalModuleDual.FullDual hA hM) :=
  NonUnitalModuleDual.fullAction hA hM

local instance : NonUnitalModule Aᵐᵒᵖ (NonUnitalModuleDual.Dual hA hM) :=
  NonUnitalModuleDual.dualAction hA hM

/-- Both pairs of actual full-fixed comparison maps are inverse as entire maps. -/
def FullFixedInverseIdentities (e : Idempotent A) : Prop :=
  letI := rightFixedModule hA hM e
  letI := fullRightFixedModule hA hM e
  (toFullFixed hA hM e).comp (fromFullFixed hA hM e) = LinearMap.id ∧
    (fromFullFixed hA hM e).comp (toFullFixed hA hM e) = LinearMap.id ∧
    (toFullFixedCorner hA hM e).comp (fromFullFixedCorner hA hM e) = LinearMap.id ∧
    (fromFullFixedCorner hA hM e).comp (toFullFixedCorner hA hM e) = LinearMap.id

/-- Prescribed equivalences keep exactly the original included functionals. -/
def FullFixedEquivalences (e : Idempotent A) : Prop :=
  letI := rightFixedModule hA hM e
  letI := fullRightFixedModule hA hM e
  ∃ E : RightFixedPart hA hM e ≃ₗ[ℂ] FullRightFixedPart hA hM e,
    ∃ C : RightFixedPart hA hM e ≃ₗ[Idempotent.Corner (oppositeIdempotent e)]
        FullRightFixedPart hA hM e,
      E.toLinearMap = toFullFixed hA hM e ∧
      E.symm.toLinearMap = fromFullFixed hA hM e ∧
      C.toLinearMap = toFullFixedCorner hA hM e ∧
      C.symm.toLinearMap = fromFullFixedCorner hA hM e ∧
      C.toLinearMap.toAddMonoidHom = E.toLinearMap.toAddMonoidHom ∧
      C.symm.toLinearMap.toAddMonoidHom = E.symm.toLinearMap.toAddMonoidHom ∧
      (NonUnitalModuleCorner.inclusion (oppositeIdempotent e)).comp
          E.toLinearMap.toAddMonoidHom =
        (NonUnitalModuleDual.inclusion hA hM).toAddMonoidHom.comp
          (NonUnitalModuleCorner.inclusion (oppositeIdempotent e)) ∧
      ((NonUnitalModuleDual.inclusion hA hM).toAddMonoidHom.comp
          (NonUnitalModuleCorner.inclusion (oppositeIdempotent e))).comp
          E.symm.toLinearMap.toAddMonoidHom =
        NonUnitalModuleCorner.inclusion (oppositeIdempotent e)

/-- The ordinary fixed-part dual has compatible, prescribed corner equivalences. -/
def CornerEquivalences (e : Idempotent A) : Prop :=
  letI := NonUnitalModuleCorner.complexModule hA hM e
  letI := rightFixedModule hA hM e
  letI := fullRightFixedModule hA hM e
  letI := fixedPartDualCornerModule hA hM e
  ∃ C : RightFixedPart hA hM e ≃ₗ[Idempotent.Corner (oppositeIdempotent e)]
      Module.Dual ℂ (FixedPart e M),
    ∃ Fℂ : FullRightFixedPart hA hM e ≃ₗ[ℂ] Module.Dual ℂ (FixedPart e M),
      ∃ FC : FullRightFixedPart hA hM e ≃ₗ[Idempotent.Corner (oppositeIdempotent e)]
          Module.Dual ℂ (FixedPart e M),
        C.toLinearMap = restrictionCorner hA hM e ∧
        C.symm.toLinearMap = extensionCorner hA hM e ∧
        C.toLinearMap.toAddMonoidHom = (restriction hA hM e).toAddMonoidHom ∧
        C.symm.toLinearMap.toAddMonoidHom = (extension hA hM e).toAddMonoidHom ∧
        Fℂ.toLinearMap = (restriction hA hM e).comp (fromFullFixed hA hM e) ∧
        Fℂ.symm.toLinearMap = (toFullFixed hA hM e).comp (extension hA hM e) ∧
        FC.toLinearMap =
          (restrictionCorner hA hM e).comp (fromFullFixedCorner hA hM e) ∧
        FC.symm.toLinearMap =
          (toFullFixedCorner hA hM e).comp (extensionCorner hA hM e) ∧
        FC.toLinearMap.toAddMonoidHom = Fℂ.toLinearMap.toAddMonoidHom ∧
        FC.symm.toLinearMap.toAddMonoidHom = Fℂ.symm.toLinearMap.toAddMonoidHom

variable {N : Type uN} [AddCommGroup N] [NonUnitalModule A N]
  (hN : IsNondegenerate A N)

local instance : NonUnitalModule Aᵐᵒᵖ (NonUnitalModuleDual.FullDual hA hN) :=
  NonUnitalModuleDual.fullAction hA hN

local instance : NonUnitalModule Aᵐᵒᵖ (NonUnitalModuleDual.Dual hA hN) :=
  NonUnitalModuleDual.dualAction hA hN

/-- Both full-fixed comparison directions and both corner-duality squares are natural. -/
def Naturality (e : Idempotent A) (f : NonUnitalModuleHom A M N) : Prop :=
  letI := NonUnitalModuleCorner.complexModule hA hM e
  letI := NonUnitalModuleCorner.complexModule hA hN e
  letI := rightFixedModule hA hM e
  letI := rightFixedModule hA hN e
  letI := fullRightFixedModule hA hM e
  letI := fullRightFixedModule hA hN e
  letI := fixedPartDualCornerModule hA hM e
  letI := fixedPartDualCornerModule hA hN e
  let RC := NonUnitalModuleCorner.restrict (oppositeIdempotent e)
    (NonUnitalModuleDual.pullback hA hM hN f)
  let SC := NonUnitalModuleCorner.restrict (oppositeIdempotent e)
    (NonUnitalModuleDual.fullPullback hA hM hN f)
  let Dℂ := (NonUnitalModuleCorner.restrictLinear hA hM hN e f).dualMap
  ∃ Rℂ : RightFixedPart hA hN e →ₗ[ℂ] RightFixedPart hA hM e,
    ∃ Sℂ : FullRightFixedPart hA hN e →ₗ[ℂ] FullRightFixedPart hA hM e,
      ∃ DC : Module.Dual ℂ (FixedPart e N) →ₗ[Idempotent.Corner (oppositeIdempotent e)]
          Module.Dual ℂ (FixedPart e M),
        Rℂ.toAddMonoidHom = RC.toAddMonoidHom ∧
        Sℂ.toAddMonoidHom = SC.toAddMonoidHom ∧
        DC.toAddMonoidHom = Dℂ.toAddMonoidHom ∧
        (toFullFixed hA hM e).comp Rℂ = Sℂ.comp (toFullFixed hA hN e) ∧
        (fromFullFixed hA hM e).comp Sℂ = Rℂ.comp (fromFullFixed hA hN e) ∧
        (toFullFixedCorner hA hM e).comp RC = SC.comp (toFullFixedCorner hA hN e) ∧
        (fromFullFixedCorner hA hM e).comp SC = RC.comp (fromFullFixedCorner hA hN e) ∧
        (restrictionCorner hA hM e).comp RC = DC.comp (restrictionCorner hA hN e) ∧
        RC.comp (extensionCorner hA hN e) = (extensionCorner hA hM e).comp DC ∧
        ((restriction hA hM e).comp (fromFullFixed hA hM e)).comp Sℂ =
          Dℂ.comp ((restriction hA hN e).comp (fromFullFixed hA hN e)) ∧
        Sℂ.comp ((toFullFixed hA hN e).comp (extension hA hN e)) =
          ((toFullFixed hA hM e).comp (extension hA hM e)).comp Dℂ

/-- Closed statement family; every scalar structure and original action is quantified. -/
def FixedPartComparisons : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (e : Idempotent A),
    FullFixedInverseIdentities hA hM e ∧
      FullFixedEquivalences hA hM e ∧
      CornerEquivalences hA hM e ∧
      ∀ (N : Type uN) [AddCommGroup N] [NonUnitalModule A N]
        (hN : IsNondegenerate A N) (f : NonUnitalModuleHom A M N),
        Naturality hA hM hN e f

/-! Complete unapplied interfaces check the predicates, without proving them. -/

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    Idempotent A → Prop := @FullFixedInverseIdentities.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    Idempotent A → Prop := @FullFixedEquivalences.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    Idempotent A → Prop := @CornerEquivalences.{uA, uM}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    Idempotent A → Prop := @FullFixedInverseIdentities.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    Idempotent A → Prop := @FullFixedInverseIdentities.{1, 0}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    Idempotent A → Prop := @FullFixedEquivalences.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    Idempotent A → Prop := @FullFixedEquivalences.{1, 0}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    Idempotent A → Prop := @CornerEquivalences.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    Idempotent A → Prop := @CornerEquivalences.{1, 0}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    {N : Type uN} → [AddCommGroup N] → [NonUnitalModule A N] →
    (hN : IsNondegenerate A N) → Idempotent A →
    NonUnitalModuleHom A M N → Prop := @Naturality.{uA, uM, uN}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    {N : Type 2} → [AddCommGroup N] → [NonUnitalModule A N] →
    (hN : IsNondegenerate A N) → Idempotent A →
    NonUnitalModuleHom A M N → Prop := @Naturality.{0, 1, 2}

example : {A : Type 2} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    {N : Type 0} → [AddCommGroup N] → [NonUnitalModule A N] →
    (hN : IsNondegenerate A N) → Idempotent A →
    NonUnitalModuleHom A M N → Prop := @Naturality.{2, 1, 0}

example : Prop := FixedPartComparisons.{uA, uM, uN}

/-! Definitional equalities check the complete closed telescope. -/

example : FixedPartComparisons.{uA, uM, uN} =
    (∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
      [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
      (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
      (hA : IsIdempotented A) (hM : IsNondegenerate A M) (e : Idempotent A),
      FullFixedInverseIdentities hA hM e ∧
        FullFixedEquivalences hA hM e ∧ CornerEquivalences hA hM e ∧
        ∀ (N : Type uN) [AddCommGroup N] [NonUnitalModule A N]
          (hN : IsNondegenerate A N) (f : NonUnitalModuleHom A M N),
          Naturality hA hM hN e f) := rfl

example : FixedPartComparisons.{0, 1, 2} =
    (∀ (A : Type 0) [NonUnitalRing A] [Module ℂ A]
      [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
      (M : Type 1) [AddCommGroup M] [NonUnitalModule A M]
      (hA : IsIdempotented A) (hM : IsNondegenerate A M) (e : Idempotent A),
      FullFixedInverseIdentities hA hM e ∧
        FullFixedEquivalences hA hM e ∧ CornerEquivalences hA hM e ∧
        ∀ (N : Type 2) [AddCommGroup N] [NonUnitalModule A N]
          (hN : IsNondegenerate A N) (f : NonUnitalModuleHom A M N),
          Naturality hA hM hN e f) := rfl

example : FixedPartComparisons.{2, 1, 0} =
    (∀ (A : Type 2) [NonUnitalRing A] [Module ℂ A]
      [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
      (M : Type 1) [AddCommGroup M] [NonUnitalModule A M]
      (hA : IsIdempotented A) (hM : IsNondegenerate A M) (e : Idempotent A),
      FullFixedInverseIdentities hA hM e ∧
        FullFixedEquivalences hA hM e ∧ CornerEquivalences hA hM e ∧
        ∀ (N : Type 0) [AddCommGroup N] [NonUnitalModule A N]
          (hN : IsNondegenerate A N) (f : NonUnitalModuleHom A M N),
          Naturality hA hM hN e f) := rfl

end Langlands.Algebra.NonUnitalModuleDualFixedPartComparisonStatements
