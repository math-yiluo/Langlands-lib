import Langlands.Algebra.IntegerCompatibleNonUnitalAction
import Langlands.Algebra.RenardAlgebraActionLocalization
import Langlands.Algebra.CompatibleUnitization
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Noetherian actual localization of additive nonunital actions

Internal derived targets motivated by Renard 2026, C.II, printed p. 279 / PDF p. 285.
The original additive action and map determine canonical integer-linear data.
All finiteness hypotheses refer explicitly to the actual integer-unitized actions.
-/

set_option autoImplicit false

namespace Langlands.Renard.AdditiveActionLocalization

open Langlands.Algebra EndomorphismLocalization AlgebraActionLocalization

universe uA uV

/-- Select the same scalar module as the generic actual localization construction.
This private alias changes no action and introduces no global instance. -/
private noncomputable abbrev actualLocalizedScalarModule
    {k : Type*} [CommRing k] {W : Type*} [AddCommGroup W] [Module k W]
    (a : Module.End k W) : Module k (Localized a) :=
  inferInstance

/-- Surjectivity of the actual canonical map and one positive exponent for its
kernel and both stability equalities, using canonical integer-linear powers. -/
def AdditiveLocalizationStabilizationAt
    {A : Type uA} [NonUnitalRing A]
    {V : Type uV} [AddCommGroup V] [NonUnitalModule A V]
    (f : NonUnitalModuleHom A V V) : Prop :=
  let a := f.toAddMonoidHom.toIntLinearMap
  letI := actualLocalizedScalarModule a
  Function.Surjective (iota a) ∧
    ∃ n : ℕ, 0 < n ∧
      LinearMap.ker (iota a) = LinearMap.ker (a ^ n) ∧
      LinearMap.ker (a ^ n) = LinearMap.ker ((a ^ n) ^ 2) ∧
      LinearMap.range (a ^ n) = LinearMap.range ((a ^ n) ^ 2)

/-- Noetherianity of the actual integer-unitized target action alone forces
the actual canonical map to be surjective. -/
def UnitizedNoetherianSurjectivityStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A]
    (V : Type uV) [AddCommGroup V] [NonUnitalModule A V]
    (f : NonUnitalModuleHom A V V),
    let ρ := NonUnitalModule.toIntLinearEndHom (A := A) (V := V)
    let a := f.toAddMonoidHom.toIntLinearMap
    letI := actualLocalizedScalarModule a
    let σ := localizedAction a ρ (fun b v => f.map_smul b v)
    letI := CompatibleUnitization.module σ
    IsNoetherian (Unitization ℤ A) (Localized a) →
      Function.Surjective (iota a)

/-- Noetherianity of the two actual integer-unitized modules gives the common
positive exponent, with no ring Noetherianity or finite-generation premise. -/
def UnitizedNoetherianStabilizationStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A]
    (V : Type uV) [AddCommGroup V] [NonUnitalModule A V]
    (f : NonUnitalModuleHom A V V),
    let ρ := NonUnitalModule.toIntLinearEndHom (A := A) (V := V)
    let a := f.toAddMonoidHom.toIntLinearMap
    letI := actualLocalizedScalarModule a
    let σ := localizedAction a ρ (fun b v => f.map_smul b v)
    letI := CompatibleUnitization.module ρ
    letI := CompatibleUnitization.module σ
    IsNoetherian (Unitization ℤ A) V →
      IsNoetherian (Unitization ℤ A) (Localized a) →
        AdditiveLocalizationStabilizationAt f

/-- Ordinary finite generation over the Noetherian integer unitization gives
the same actual canonical-map and common-exponent conclusion. -/
def UnitizedFiniteStabilizationStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A]
    (V : Type uV) [AddCommGroup V] [NonUnitalModule A V]
    (f : NonUnitalModuleHom A V V),
    let ρ := NonUnitalModule.toIntLinearEndHom (A := A) (V := V)
    let a := f.toAddMonoidHom.toIntLinearMap
    letI := actualLocalizedScalarModule a
    let σ := localizedAction a ρ (fun b v => f.map_smul b v)
    letI := CompatibleUnitization.module ρ
    letI := CompatibleUnitization.module σ
    IsNoetherianRing (Unitization ℤ A) →
      Module.Finite (Unitization ℤ A) V →
      Module.Finite (Unitization ℤ A) (Localized a) →
        AdditiveLocalizationStabilizationAt f

/-- The closed internal actual-localization targets for original additive actions. -/
def AdditiveLocalizationNoetherianStatements : Prop :=
  UnitizedNoetherianSurjectivityStatement.{uA, uV} ∧
    UnitizedNoetherianStabilizationStatement.{uA, uV} ∧
    UnitizedFiniteStabilizationStatement.{uA, uV}

end Langlands.Renard.AdditiveActionLocalization
