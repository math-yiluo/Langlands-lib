import Langlands.Algebra.CompatibleUnitization
import Langlands.Algebra.NonUnitalPowers
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Renard B.III: separation for the original nonunital action

The source is Renard, French version dated 9 July 2026, Appendix B.III,
printed p. 273 / PDF p. 279, with the additive-module conventions of printed
pp. 5–6 and I.2.1. The witness is the actual regular-left-module quotient
`Unitization ℂ A ⧸ I`. Its original `A`-action is the restriction of the
canonical quotient action along `Unitization.inr`. Simplicity is asserted
for every stable additive subgroup, not just complex vector subspaces.

The three proposition targets state the original one-sided shift, the
actual separating quotient with its additive restriction, and separation.
The aggregate is derived implementation packaging. No target is proved here.
-/

set_option autoImplicit false

universe uA

namespace Langlands.Renard

open Langlands.Algebra

/-- The one-sided shift in the actual scalar unitization, for an element
which is nonnilpotent in the original possibly nonunital algebra. -/
@[pp_with_univ]
def NonUnitalNonnilpotentLeftResolventStatement
    (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] : Prop :=
  Module.rank ℂ A ≤ Cardinal.aleph0 →
    ∀ a : A, ¬ IsNonUnitalNilpotent a →
      ∃ z : ℂ, z ≠ 0 ∧
        ∀ b : Unitization ℂ A,
          b * ((Unitization.inr a : Unitization ℂ A) -
            algebraMap ℂ (Unitization ℂ A) z) ≠ 1

/-- A nonzero scalar shift without a left inverse gives an actual simple
unitized quotient whose restricted original action is additively simple
and moves the actual class of `1`. No dimension or nilpotence assumption
is needed in this quotient step. -/
@[pp_with_univ]
def NonUnitalLeftShiftSimpleQuotientStatement
    (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] : Prop :=
  ∀ (a : A) (z : ℂ), z ≠ 0 →
    (∀ b : Unitization ℂ A,
      b * ((Unitization.inr a : Unitization ℂ A) -
        algebraMap ℂ (Unitization ℂ A) z) ≠ 1) →
    ∃ I : Submodule (Unitization ℂ A) (Unitization ℂ A),
      IsCoatom I ∧
      Submodule.span (Unitization ℂ A)
        {(Unitization.inr a : Unitization ℂ A) -
          algebraMap ℂ (Unitization ℂ A) z} ≤ I ∧
      IsSimpleModule (Unitization ℂ A) (Unitization ℂ A ⧸ I) ∧
      (let ρ : A →ₙₐ[ℂ] Module.End ℂ (Unitization ℂ A ⧸ I) :=
        Unitization.lift.symm (_root_.Algebra.lsmul ℂ ℂ (Unitization ℂ A ⧸ I))
       letI := NonUnitalModule.ofLinearEndHom ρ
       Nontrivial (Unitization ℂ A ⧸ I) ∧
         (∀ S : NonUnitalSubmodule A (Unitization ℂ A ⧸ I),
           S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤) ∧
         a • I.mkQ 1 ≠ 0)

/-- Renard B.III for the original nonunital algebra and additive action,
with the simple module realized as the actual scalar-unitization quotient
constructed in the source proof and the separating vector the class of `1`. -/
@[pp_with_univ]
def NonUnitalSeparationStatement
    (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] : Prop :=
  Module.rank ℂ A ≤ Cardinal.aleph0 →
    ∀ a : A, ¬ IsNonUnitalNilpotent a →
      ∃ I : Submodule (Unitization ℂ A) (Unitization ℂ A),
        IsCoatom I ∧
        IsSimpleModule (Unitization ℂ A) (Unitization ℂ A ⧸ I) ∧
        (let ρ : A →ₙₐ[ℂ] Module.End ℂ (Unitization ℂ A ⧸ I) :=
          Unitization.lift.symm (_root_.Algebra.lsmul ℂ ℂ (Unitization ℂ A ⧸ I))
         letI := NonUnitalModule.ofLinearEndHom ρ
         Nontrivial (Unitization ℂ A ⧸ I) ∧
           (∀ S : NonUnitalSubmodule A (Unitization ℂ A ⧸ I),
             S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤) ∧
           a • I.mkQ 1 ≠ 0)

/-- The three targets, universally quantified over the arbitrary original
algebra universe. The witness quotient is in that same universe because
it is the actual quotient of `Unitization ℂ A`. -/
@[pp_with_univ]
def NonUnitalSeparationReductionStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A],
    NonUnitalNonnilpotentLeftResolventStatement A ∧
    NonUnitalLeftShiftSimpleQuotientStatement A ∧
    NonUnitalSeparationStatement A

-- Check the complete, unapplied telescope of each component.
example : (A : Type uA) → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] → Prop :=
  @NonUnitalNonnilpotentLeftResolventStatement

example : (A : Type uA) → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] → Prop :=
  @NonUnitalLeftShiftSimpleQuotientStatement

example : (A : Type uA) → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] → Prop :=
  @NonUnitalSeparationStatement

section QuotientActionChecks

variable (A : Type uA) [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  (I : Submodule (Unitization ℂ A) (Unitization ℂ A))

-- The complex structure and scalar tower are the canonical quotient instances.
example : Module ℂ (Unitization ℂ A ⧸ I) := inferInstance

example : IsScalarTower ℂ (Unitization ℂ A) (Unitization ℂ A ⧸ I) :=
  inferInstance

-- Restriction uses the actual quotient action along the actual embedding.
example (a : A) (m : Unitization ℂ A ⧸ I) :
    let ρ : A →ₙₐ[ℂ] Module.End ℂ (Unitization ℂ A ⧸ I) :=
      Unitization.lift.symm (_root_.Algebra.lsmul ℂ ℂ (Unitization ℂ A ⧸ I))
    letI := NonUnitalModule.ofLinearEndHom ρ
    a • m = (Unitization.inr a : Unitization ℂ A) • m := rfl

-- The source's separating vector is the actual class of the unit.
example (a : A) :
    let ρ : A →ₙₐ[ℂ] Module.End ℂ (Unitization ℂ A ⧸ I) :=
      Unitization.lift.symm (_root_.Algebra.lsmul ℂ ℂ (Unitization ℂ A ⧸ I))
    letI := NonUnitalModule.ofLinearEndHom ρ
    a • I.mkQ 1 = I.mkQ (Unitization.inr a) := by
  dsimp only
  change (Unitization.inr a : Unitization ℂ A) • I.mkQ 1 = _
  rw [← LinearMap.map_smul, smul_eq_mul, mul_one]

end QuotientActionChecks

end Langlands.Renard
