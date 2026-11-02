import Langlands.Algebra.CompatibleUnitizationSubmodule
import Langlands.Algebra.NonUnitalModuleSubobject
import Langlands.Algebra.NonUnitalModuleAdditive
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.CategoryTheory.Simple

/-!
# Simplicity and scalar linearity for the actual unitized action

These are derived proposition targets for the nonunital reductions in Renard I.2.1 and
Appendix B.II–III (French version dated 9 July 2026). Stable vector subspaces and stable
additive subgroups are kept distinct. The restriction and automatic-linearity targets
require a nonzero original action. No target is proved or assumed here.
-/

set_option autoImplicit false

namespace Langlands.Algebra.CompatibleUnitization

universe uK uA uM uN

section General

variable {k : Type uK} [Field k] {A : Type uA} [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]
  {M : Type uM} [AddCommGroup M] [Module k M]

/-- Simplicity of stable vector subspaces is exactly simplicity of the actual unitized
module. `IsSimpleOrder` excludes a one-element subspace lattice. -/
def CompatibleSimpleUnitizationStatement (ρ : A →ₙₐ[k] Module.End k M) : Prop :=
  IsSimpleOrder (CompatibleSubmodule ρ) ↔
    (letI := module ρ; IsSimpleModule (Unitization k A) M)

/-- Simplicity of all original stable additive subgroups is categorical simplicity in the
existing additive nonunital module category, for precisely the chosen action. -/
def AdditiveSimpleCategoricalStatement (ρ : A →ₙₐ[k] Module.End k M) : Prop :=
  letI := NonUnitalModule.ofLinearEndHom ρ
  (Nontrivial M ∧ ∀ S : NonUnitalSubmodule A M,
      S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤) ↔
    CategoryTheory.Simple (NonUnitalModuleCat.of A M)

/-- Original additive simplicity implies simplicity after the actual scalar unitization. -/
def AdditiveSimpleUnitizationStatement (ρ : A →ₙₐ[k] Module.End k M) : Prop :=
  (letI := NonUnitalModule.ofLinearEndHom ρ; (Nontrivial M ∧ ∀ S : NonUnitalSubmodule A M,
      S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤)) →
    (letI := module ρ; IsSimpleModule (Unitization k A) M)

/-- Restricting a simple unitized module to a nonzero original action is additively simple.
The explicit nonzero-action premise is essential over a general field. -/
def SimpleUnitizationRestrictionStatement (ρ : A →ₙₐ[k] Module.End k M) : Prop :=
  ρ ≠ 0 → (letI := module ρ; IsSimpleModule (Unitization k A) M) →
    (letI := NonUnitalModule.ofLinearEndHom ρ; (Nontrivial M ∧ ∀ S : NonUnitalSubmodule A M,
      S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤))

/-- With a nonzero original action, every nonzero vector of a simple unitized module is
cyclic already under `A`: the actual original-action orbit map is surjective. -/
def SimpleUnitizationOrbitStatement (ρ : A →ₙₐ[k] Module.End k M) : Prop :=
  ρ ≠ 0 → (letI := module ρ; IsSimpleModule (Unitization k A) M) →
    ∀ m : M, m ≠ 0 → Function.Surjective (fun a : A => ρ a m)

/-- Every additive original-action intertwiner from a simple unitized source with nonzero
original action preserves the separately specified field scalars. No simplicity or
nonzero-action condition is imposed on the target. -/
def SimpleUnitizationIntertwinerStatement (ρ : A →ₙₐ[k] Module.End k M) : Prop :=
  ρ ≠ 0 → (letI := module ρ; IsSimpleModule (Unitization k A) M) →
    ∀ (N : Type uN) [AddCommGroup N] [Module k N]
      (σ : A →ₙₐ[k] Module.End k N),
      letI := NonUnitalModule.ofLinearEndHom ρ
      letI := NonUnitalModule.ofLinearEndHom σ
      ∀ f : NonUnitalModuleHom A M N, ∀ (c : k) (m : M), f (c • m) = c • f m

end General

/-- In the complex-vector-space setting, a simple original additive module cannot have
zero original action. This is a derived bridge, not an added hypothesis of B.II. -/
def ComplexAdditiveSimpleActionNonzeroStatement : Prop :=
  ∀ {A : Type uA} [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    {M : Type uM} [AddCommGroup M] [Module ℂ M]
    (ρ : A →ₙₐ[ℂ] Module.End ℂ M),
    (letI := NonUnitalModule.ofLinearEndHom ρ; (Nontrivial M ∧ ∀ S : NonUnitalSubmodule A M,
      S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤)) →
      ρ ≠ 0

/-- The seven separate derived bridges, universally quantified over independent scalar,
algebra, source and target carrier universes. -/
def NonUnitalSimplicityReductionStatement : Prop :=
  (∀ {k : Type uK} [Field k] {A : Type uA} [NonUnitalRing A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    {M : Type uM} [AddCommGroup M] [Module k M]
    (ρ : A →ₙₐ[k] Module.End k M),
      CompatibleSimpleUnitizationStatement ρ ∧
      AdditiveSimpleCategoricalStatement ρ ∧
      AdditiveSimpleUnitizationStatement ρ ∧
      SimpleUnitizationRestrictionStatement ρ ∧
      SimpleUnitizationOrbitStatement ρ ∧
      SimpleUnitizationIntertwinerStatement.{uK, uA, uM, uN} ρ) ∧
    ComplexAdditiveSimpleActionNonzeroStatement.{uA, uM}

end Langlands.Algebra.CompatibleUnitization
