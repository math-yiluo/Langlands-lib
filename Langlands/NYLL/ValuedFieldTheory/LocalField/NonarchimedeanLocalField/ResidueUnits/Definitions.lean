/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Adapted by Worker 126 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709,
-- ResidueUnits.lean, lines 26-42, 52-87 and 135-138 (M137.001-.003, .005-.009, .015).
-- See Definitions.md for the exact source lines, modifications and licenses/NYLL/.

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# Residue units and integer units modulo first principal units

The residue-field unit group `𝓀[K]ˣ`, the quotient `𝒪[K]ˣ ⧸ U¹` of valuation-ring units by
the first principal units, their commutative group structures and concrete comparisons, the
class map, and reduction of valuation-ring units to residue-field units.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The residue-field unit group attached to a valued field. -/
def ResidueUnits (K : Type u) [Field K] [ValuativeRel K] : Type u :=
  𝓀[K]ˣ

/-- The unit group of the residue field is a commutative group. -/
instance residueUnitsCommGroup
    (K : Type u) [Field K] [ValuativeRel K] :
    CommGroup (ResidueUnits K) := by
  change CommGroup 𝓀[K]ˣ
  infer_instance

/-- Explicit comparison with the concrete unit group of the residue field. -/
def residueUnitsConcreteEquiv
    (K : Type u) [Field K] [ValuativeRel K] :
    ResidueUnits K ≃* 𝓀[K]ˣ := by
  change 𝓀[K]ˣ ≃* 𝓀[K]ˣ
  exact MulEquiv.refl _

/-- The unit group of the finite residue field is finite. -/
noncomputable instance residueUnitsFinite
    (K : Type u) [Field K] [ValuativeRel K] [Finite 𝓀[K]] :
    Finite (ResidueUnits K) := by
  exact Finite.of_equiv 𝓀[K]ˣ (residueUnitsConcreteEquiv K).symm.toEquiv

/-- Integer units modulo first principal units. -/
@[implicit_reducible]
def IntegerUnitsModPrincipalUnits
    (K : Type u) [Field K] [ValuativeRel K] : Type u :=
  𝒪[K]ˣ ⧸ principalUnits K 1

/-- Valuation-ring units modulo first principal units form a commutative quotient group. -/
@[implicit_reducible]
instance integerUnitsModPrincipalUnitsCommGroup
    (K : Type u) [Field K] [ValuativeRel K] :
    CommGroup (IntegerUnitsModPrincipalUnits K) := by
  change CommGroup (𝒪[K]ˣ ⧸ principalUnits K 1)
  infer_instance

/-- Explicit access to the concrete quotient model. -/
def integerUnitsModPrincipalUnitsConcreteEquiv
    (K : Type u) [Field K] [ValuativeRel K] :
    IntegerUnitsModPrincipalUnits K ≃*
      (𝒪[K]ˣ ⧸ principalUnits K 1) := by
  change (𝒪[K]ˣ ⧸ principalUnits K 1) ≃*
    (𝒪[K]ˣ ⧸ principalUnits K 1)
  exact MulEquiv.refl _

/-- The canonical class of an integer unit modulo first principal units. -/
@[implicit_reducible]
def integerUnitsModPrincipalUnitsMk
    (K : Type u) [Field K] [ValuativeRel K] :
    𝒪[K]ˣ →* IntegerUnitsModPrincipalUnits K := by
  change 𝒪[K]ˣ →* (𝒪[K]ˣ ⧸ principalUnits K 1)
  exact QuotientGroup.mk' (principalUnits K 1)

/-- Reduction of valuation-integer units to residue-field units. -/
def integerUnitsToResidueUnits (K : Type u) [Field K] [ValuativeRel K] :
    𝒪[K]ˣ →* ResidueUnits K :=
  Units.map (IsLocalRing.residue 𝒪[K]).toMonoidHom

end

end Langlands.NYLL.LocalFieldTheory
