import Langlands.Algebra.NonUnitalSimplicityStatements
import Mathlib.LinearAlgebra.Dimension.Basic

/-!
# Renard B.II for the original nonunital action

These proposition targets retain all additive original-action endomorphisms, rather than
assuming scalar linearity of those endomorphisms. Simplicity means nontriviality and
simplicity of every stable additive subgroup. The centralizer is the published actual
complex-linear endomorphism algebra of the specified action. No assertion is proved here.
-/

set_option autoImplicit false

namespace Langlands.Renard

open Langlands.Algebra
open Langlands.Algebra.CompatibleUnitization

universe uA uM

/-- B.II a): the ring of all additive original-action endomorphisms is a division ring.
Its multiplication and identity are those of the actual categorical endomorphism ring. -/
def NonUnitalSchurEndDivisionStatement
    {A : Type uA} [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    {M : Type uM} [AddCommGroup M] [Module ℂ M]
    (ρ : A →ₙₐ[ℂ] Module.End ℂ M) : Prop :=
  letI := NonUnitalModule.ofLinearEndHom ρ
  (Nontrivial M ∧ ∀ S : NonUnitalSubmodule A M,
      S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤) →
    Nontrivial (CategoryTheory.End (NonUnitalModuleCat.of A M)) ∧
      ∀ f : CategoryTheory.End (NonUnitalModuleCat.of A M), f ≠ 0 → IsUnit f

/-- B.II, kernel/image step for all original additive endomorphisms. -/
def NonUnitalSchurEndBijectiveStatement
    {A : Type uA} [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    {M : Type uM} [AddCommGroup M] [Module ℂ M]
    (ρ : A →ₙₐ[ℂ] Module.End ℂ M) : Prop :=
  letI := NonUnitalModule.ofLinearEndHom ρ
  (Nontrivial M ∧ ∀ S : NonUnitalSubmodule A M,
      S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤) →
    ∀ f : NonUnitalModuleHom A M M, f ≠ 0 → Function.Bijective f

/-- Derived actual-map comparison: every additive original-action endomorphism of a
simple complex module comes from a unique element of the published centralizer. -/
def NonUnitalSchurEndComparisonStatement
    {A : Type uA} [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    {M : Type uM} [AddCommGroup M] [Module ℂ M]
    (ρ : A →ₙₐ[ℂ] Module.End ℂ M) : Prop :=
  letI := NonUnitalModule.ofLinearEndHom ρ
  (Nontrivial M ∧ ∀ S : NonUnitalSubmodule A M,
      S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤) →
    ∀ f : NonUnitalModuleHom A M M,
      ∃! g : centralizer ρ, ∀ m : M, (g : Module.End ℂ M) m = f m

/-- B.II, original cyclic action map: every nonzero vector is reached from the original
algebra, before adjoining the scalar unit. -/
def NonUnitalSchurCyclicMapSurjectiveStatement
    {A : Type uA} [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    {M : Type uM} [AddCommGroup M] [Module ℂ M]
    (ρ : A →ₙₐ[ℂ] Module.End ℂ M) : Prop :=
  (letI := NonUnitalModule.ofLinearEndHom ρ;
    Nontrivial M ∧ ∀ S : NonUnitalSubmodule A M,
      S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤) →
    ∀ m : M, m ≠ 0 → Function.Surjective (fun a : A => ρ a m)

/-- B.II, actual evaluation on the original-action complex centralizer is injective at
every nonzero vector of an additively simple original module. -/
def NonUnitalSchurEvaluationInjectiveStatement
    {A : Type uA} [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    {M : Type uM} [AddCommGroup M] [Module ℂ M]
    (ρ : A →ₙₐ[ℂ] Module.End ℂ M) : Prop :=
  (letI := NonUnitalModule.ofLinearEndHom ρ;
    Nontrivial M ∧ ∀ S : NonUnitalSubmodule A M,
      S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤) →
    ∀ m : M, m ≠ 0 →
      Function.Injective (fun g : centralizer ρ => (g : Module.End ℂ M) m)

/-- B.II, countable dimension of the original algebra suffices for countable dimension
of the original simple complex module. -/
def NonUnitalSchurModuleRankCountableStatement
    {A : Type uA} [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    {M : Type uM} [AddCommGroup M] [Module ℂ M]
    (ρ : A →ₙₐ[ℂ] Module.End ℂ M) : Prop :=
  (letI := NonUnitalModule.ofLinearEndHom ρ;
    Nontrivial M ∧ ∀ S : NonUnitalSubmodule A M,
      S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤) →
    Module.rank ℂ A ≤ Cardinal.aleph0 → Module.rank ℂ M ≤ Cardinal.aleph0

/-- B.II, countable dimension passes from the original module to its actual
complex-linear endomorphism algebra. The comparison target also retains all additive
endomorphisms without choosing a scalar-module instance on their type. -/
def NonUnitalSchurEndRankCountableStatement
    {A : Type uA} [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    {M : Type uM} [AddCommGroup M] [Module ℂ M]
    (ρ : A →ₙₐ[ℂ] Module.End ℂ M) : Prop :=
  (letI := NonUnitalModule.ofLinearEndHom ρ;
    Nontrivial M ∧ ∀ S : NonUnitalSubmodule A M,
      S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤) →
    Module.rank ℂ M ≤ Cardinal.aleph0 →
      Module.rank ℂ (centralizer ρ) ≤ Cardinal.aleph0

/-- B.II b): the actual scalar algebra map is bijective, and every additive original
endomorphism is multiplication by a unique complex scalar, under module countability. -/
def NonUnitalSchurScalarOfModuleRankCountableStatement
    {A : Type uA} [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    {M : Type uM} [AddCommGroup M] [Module ℂ M]
    (ρ : A →ₙₐ[ℂ] Module.End ℂ M) : Prop :=
  letI := NonUnitalModule.ofLinearEndHom ρ
  (Nontrivial M ∧ ∀ S : NonUnitalSubmodule A M,
      S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤) →
    Module.rank ℂ M ≤ Cardinal.aleph0 →
      Function.Bijective (algebraMap ℂ (centralizer ρ)) ∧
        ∀ f : NonUnitalModuleHom A M M, ∃! z : ℂ, ∀ m : M, f m = z • m

/-- B.II, final sentence: countable dimension of the original algebra suffices for both
the canonical scalar-map assertion and scalarity of all additive original endomorphisms. -/
def NonUnitalSchurScalarOfAlgebraRankCountableStatement
    {A : Type uA} [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    {M : Type uM} [AddCommGroup M] [Module ℂ M]
    (ρ : A →ₙₐ[ℂ] Module.End ℂ M) : Prop :=
  letI := NonUnitalModule.ofLinearEndHom ρ
  (Nontrivial M ∧ ∀ S : NonUnitalSubmodule A M,
      S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤) →
    Module.rank ℂ A ≤ Cardinal.aleph0 →
      Function.Bijective (algebraMap ℂ (centralizer ρ)) ∧
        ∀ f : NonUnitalModuleHom A M M, ∃! z : ℂ, ∀ m : M, f m = z • m

/-- The original-action Schur theorem together with its actual-map comparison and
cyclic/evaluation/countability auxiliaries, at independent algebra and module universes. -/
def NonUnitalSchurStatement : Prop :=
  ∀ {A : Type uA} [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    {M : Type uM} [AddCommGroup M] [Module ℂ M]
    (ρ : A →ₙₐ[ℂ] Module.End ℂ M),
      NonUnitalSchurEndDivisionStatement ρ ∧
      NonUnitalSchurEndBijectiveStatement ρ ∧
      NonUnitalSchurEndComparisonStatement ρ ∧
      NonUnitalSchurCyclicMapSurjectiveStatement ρ ∧
      NonUnitalSchurEvaluationInjectiveStatement ρ ∧
      NonUnitalSchurModuleRankCountableStatement ρ ∧
      NonUnitalSchurEndRankCountableStatement ρ ∧
      NonUnitalSchurScalarOfModuleRankCountableStatement ρ ∧
      NonUnitalSchurScalarOfAlgebraRankCountableStatement ρ

end Langlands.Renard
