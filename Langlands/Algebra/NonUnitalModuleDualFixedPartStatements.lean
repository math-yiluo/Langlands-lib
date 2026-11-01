import Langlands.Algebra.NonUnitalModuleDualFixedPartMaps
import Langlands.Algebra.NonUnitalModuleDualMap

/-!
Canonical fixed-part duality statement targets for Renard I.4.1.
Adapted by Worker 1156 from Worker 6's private typing audit.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDualFixedPart

open NonUnitalModuleCorner (FixedPart)
open NonUnitalModuleDualFixedPartMaps

universe uA uM uN

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M)

/-- Both complete linear-map inverse equations for canonical restriction and extension. -/
def InverseIdentities (e : Idempotent A) : Prop :=
  letI := NonUnitalModuleCorner.complexModule hA hM e
  letI := rightFixedModule hA hM e
  (restriction hA hM e).comp (extension hA hM e) = LinearMap.id ∧
    (extension hA hM e).comp (restriction hA hM e) = LinearMap.id

/-- A complex-linear equivalence whose entire forward and inverse maps are prescribed. -/
def EquivalenceExists (e : Idempotent A) : Prop :=
  letI := NonUnitalModuleCorner.complexModule hA hM e
  letI := rightFixedModule hA hM e
  ∃ E : RightFixedPart hA hM e ≃ₗ[ℂ] Module.Dual ℂ (FixedPart e M),
    E.toLinearMap = restriction hA hM e ∧
      E.symm.toLinearMap = extension hA hM e

variable {N : Type uN} [AddCommGroup N] [NonUnitalModule A N]
  (hN : IsNondegenerate A N)

local instance : NonUnitalModule Aᵐᵒᵖ (NonUnitalModuleDual.FullDual hA hM) :=
  NonUnitalModuleDual.fullAction hA hM

local instance : NonUnitalModule Aᵐᵒᵖ (NonUnitalModuleDual.FullDual hA hN) :=
  NonUnitalModuleDual.fullAction hA hN

local instance : NonUnitalModule Aᵐᵒᵖ (NonUnitalModuleDual.Dual hA hM) :=
  NonUnitalModuleDual.dualAction hA hM

local instance : NonUnitalModule Aᵐᵒᵖ (NonUnitalModuleDual.Dual hA hN) :=
  NonUnitalModuleDual.dualAction hA hN

/-- Original restricted pullback is linear, and both entire naturality squares commute. -/
def Naturality (e : Idempotent A) (f : NonUnitalModuleHom A M N) : Prop :=
  letI := NonUnitalModuleCorner.complexModule hA hM e
  letI := NonUnitalModuleCorner.complexModule hA hN e
  letI := rightFixedModule hA hM e
  letI := rightFixedModule hA hN e
  ∃ T : RightFixedPart hA hN e →ₗ[ℂ] RightFixedPart hA hM e,
    T.toAddMonoidHom =
      (NonUnitalModuleCorner.restrict (oppositeIdempotent e)
        (NonUnitalModuleDual.pullback hA hM hN f)).toAddMonoidHom ∧
    (restriction hA hM e).comp T =
      (NonUnitalModuleCorner.restrictLinear hA hM hN e f).dualMap.comp
        (restriction hA hN e) ∧
    T.comp (extension hA hN e) =
      (extension hA hM e).comp
        (NonUnitalModuleCorner.restrictLinear hA hM hN e f).dualMap

/-- Closed family of the three explicit assertions, with independent universes. -/
def FixedPartDuality : Prop :=
  ∀ {A : Type uA} [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (e : Idempotent A),
    InverseIdentities hA hM e ∧ EquivalenceExists hA hM e ∧
      ∀ {N : Type uN} [AddCommGroup N] [NonUnitalModule A N]
        (hN : IsNondegenerate A N) (f : NonUnitalModuleHom A M N),
        Naturality hA hM hN e f

/- Complete unapplied interfaces. These check predicates, not their truth. -/

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    Idempotent A → Prop := @InverseIdentities.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    Idempotent A → Prop := @EquivalenceExists.{uA, uM}

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

example : Prop := FixedPartDuality.{uA, uM, uN}

end Langlands.Algebra.NonUnitalModuleDualFixedPart
