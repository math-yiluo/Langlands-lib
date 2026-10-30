import Langlands.Algebra.IntegerCompatibleNonUnitalAction
import Langlands.Algebra.RenardAlgebraActionLocalization
import Langlands.Algebra.CompatibleSubmodule
import Langlands.Algebra.CompatibleUnitization

/-!
# The canonical compatible stable image for additive nonunital actions

Internal finiteness-free targets motivated by Renard 2026, C.II, printed
p. 279 / PDF p. 285. Original additive actions and intertwiners determine
the canonical integer-linear data and their actual localization.
-/

set_option autoImplicit false

namespace Langlands.Renard.AdditiveActionLocalization

open Langlands.Algebra EndomorphismLocalization AlgebraActionLocalization

universe uA uV

/-- Select the existing scalar module of the generic actual localization.
This private alias changes no action and introduces no global instance. -/
private noncomputable abbrev actualLocalizedScalarModule
    {k : Type*} [CommRing k] {W : Type*} [AddCommGroup W] [Module k W]
    (a : Module.End k W) : Module k (Localized a) :=
  inferInstance

/-- Complementarity and the unique original-action-compatible,
operator-compatible equivalence normalized by the actual canonical map. -/
def AdditiveStablePowerImageAt
    {A : Type uA} [NonUnitalRing A]
    {V : Type uV} [AddCommGroup V] [NonUnitalModule A V]
    (f : NonUnitalModuleHom A V V) (n : ℕ) : Prop :=
  let ρ := NonUnitalModule.toIntLinearEndHom (A := A) (V := V)
  let a := f.toAddMonoidHom.toIntLinearMap
  letI := actualLocalizedScalarModule a
  let σ := localizedAction a ρ (fun b v => f.map_smul b v)
  letI := CompatibleUnitization.module ρ
  let powers : ℕ → LinearIntertwiner ρ ρ := fun m =>
    CompatibleUnitization.toLinearIntertwiner
      ((CompatibleUnitization.ofLinearIntertwiner f.toIntLinearIntertwiner) ^ m)
  let K := (powers n).ker
  let I := (powers n).range
  IsCompl K I ∧
    ∃! e : Localized a ≃ₗ[ℤ] I.toSubmodule,
      (∀ b z, e (σ b z) = I.restrictAction b (e z)) ∧
        I.toSubmodule.subtype.comp (e.toLinearMap.comp (localizedEnd a)) =
          a.comp (I.toSubmodule.subtype.comp e.toLinearMap) ∧
        e.symm.toLinearMap = (iota a).comp I.toSubmodule.subtype

/-- A positive power stable in kernel and image gives the canonical
compatible stable image, using only the original additive data. -/
def AdditiveStablePowerImageStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A]
    (V : Type uV) [AddCommGroup V] [NonUnitalModule A V]
    (f : NonUnitalModuleHom A V V) (n : ℕ),
    let a := f.toAddMonoidHom.toIntLinearMap
    0 < n →
      LinearMap.ker (a ^ n) = LinearMap.ker ((a ^ n) ^ 2) →
      LinearMap.range (a ^ n) = LinearMap.range ((a ^ n) ^ 2) →
      AdditiveStablePowerImageAt f n

end Langlands.Renard.AdditiveActionLocalization
