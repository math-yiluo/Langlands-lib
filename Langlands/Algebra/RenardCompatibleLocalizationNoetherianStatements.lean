import Langlands.Algebra.RenardAlgebraActionLocalization
import Langlands.Algebra.CompatibleSubmodule
import Langlands.Algebra.CompatibleUnitization
import Langlands.LinearAlgebra.StableEndomorphismStatements
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Noetherian unitized actions on actual endomorphism localization

Internal derived statement targets motivated by Renard 2026, C.II,
printed p. 279 / PDF p. 285. The actual compatible actions are unitized
locally; no identification with the source's finiteness conventions is made.
-/

set_option autoImplicit false

namespace Langlands.Renard.AlgebraActionLocalization

open Langlands.Algebra EndomorphismLocalization
open Langlands.LinearAlgebra.StableEndomorphism

universe uB uV

/-- Surjectivity and a common positive kernel/stability exponent for the
actual canonical map and the actual compatible powers. -/
def CompatibleLocalizationStabilizationAt
    {B : Type uB} [NonUnitalRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (f : LinearIntertwiner ρ ρ) : Prop :=
  let a := f.toLinearMap
  let ha : ∀ b z, a (ρ b z) = ρ b (a z) := fun b z => f.map_action' b z
  letI := CompatibleUnitization.module ρ
  let powers : ℕ → LinearIntertwiner ρ ρ := fun n =>
    CompatibleUnitization.toLinearIntertwiner
      ((CompatibleUnitization.ofLinearIntertwiner f) ^ n)
  Function.Surjective (iota a) ∧
    ∃ n : ℕ, 0 < n ∧
      (iotaIntertwiner a ρ ha).ker = (powers n).ker ∧ Stable (a ^ n)

/-- Noetherianity of the actual unitized target alone forces the actual
canonical map to be surjective. -/
def UnitizedNoetherianSurjectivityStatement : Prop :=
  ∀ (B : Type uB) [NonUnitalRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (f : LinearIntertwiner ρ ρ),
    let a := f.toLinearMap
    let ha : ∀ b z, a (ρ b z) = ρ b (a z) := fun b z => f.map_action' b z
    let σ := localizedAction a ρ ha
    letI := CompatibleUnitization.module σ
    IsNoetherian (Unitization ℂ B) (Localized a) →
      Function.Surjective (iota a)

/-- Noetherianity of the two actual unitized modules gives the common
positive exponent, without ring Noetherianity or finite generation. -/
def UnitizedNoetherianStabilizationStatement : Prop :=
  ∀ (B : Type uB) [NonUnitalRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (f : LinearIntertwiner ρ ρ),
    let a := f.toLinearMap
    let ha : ∀ b z, a (ρ b z) = ρ b (a z) := fun b z => f.map_action' b z
    let σ := localizedAction a ρ ha
    letI := CompatibleUnitization.module ρ
    letI := CompatibleUnitization.module σ
    IsNoetherian (Unitization ℂ B) V →
      IsNoetherian (Unitization ℂ B) (Localized a) →
        CompatibleLocalizationStabilizationAt ρ f

/-- Ordinary finite generation over the actual Noetherian unitization
implies the same actual-map and common-exponent conclusion. -/
def UnitizedFiniteStabilizationStatement : Prop :=
  ∀ (B : Type uB) [NonUnitalRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (f : LinearIntertwiner ρ ρ),
    let a := f.toLinearMap
    let ha : ∀ b z, a (ρ b z) = ρ b (a z) := fun b z => f.map_action' b z
    let σ := localizedAction a ρ ha
    letI := CompatibleUnitization.module ρ
    letI := CompatibleUnitization.module σ
    IsNoetherianRing (Unitization ℂ B) →
      Module.Finite (Unitization ℂ B) V →
      Module.Finite (Unitization ℂ B) (Localized a) →
        CompatibleLocalizationStabilizationAt ρ f

/-- The closed internal actual-localization Noetherian adapter targets. -/
def CompatibleLocalizationNoetherianStatements : Prop :=
  UnitizedNoetherianSurjectivityStatement.{uB, uV} ∧
    UnitizedNoetherianStabilizationStatement.{uB, uV} ∧
    UnitizedFiniteStabilizationStatement.{uB, uV}

end Langlands.Renard.AlgebraActionLocalization
