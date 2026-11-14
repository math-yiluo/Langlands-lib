/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration.Definitions
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The first principal-unit quotient

Adapted by Worker 713 using Worker 298's construction recipe from NYLL
M225.009 and M228.002 at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
Modifications: add the `Langlands.NYLL` namespace prefix, isolate the two data
declarations, import the published principal-unit subgroup and Mathlib directly,
and prove the needed kernel equality locally using the canonical residue map.
The residue-unit homomorphism and quotient-equivalence construction are retained.
The original license and notices are in `licenses/NYLL/`.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

variable {K : Type u} [Field K]
variable (F : Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- The residue of a valuation-ring unit, viewed as a unit of the residue field. -/
def residueUnitHom : F.valuationSubringˣ →* F.residueFieldˣ :=
  Units.map F.residueMap.toMonoidHom

/-- The first-isomorphism form of the residue map on valuation-ring units:
`O_K^* / U_K^1` is the unit group of the residue field. -/
def unitsModOneEquivResidueFieldUnits :
    F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F 1 ≃* F.residueFieldˣ := by
  have hk : (residueUnitHom F).ker = higherPrincipalUnitGroup F 1 := by
    ext a
    change Units.map F.residueMap.toMonoidHom a = 1 ↔
      (a : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ 1
    rw [pow_one]
    constructor
    · intro h
      have hval : F.residueMap (a : F.valuationSubring) = 1 :=
        congrArg (fun z : F.residueFieldˣ => (z : F.residueField)) h
      apply (IsLocalRing.residue_eq_zero_iff _).1
      change F.residueMap ((a : F.valuationSubring) - 1) = 0
      rw [map_sub, map_one, hval, sub_self]
    · intro h
      apply Units.ext
      change F.residueMap (a : F.valuationSubring) = 1
      have hz := (IsLocalRing.residue_eq_zero_iff _).2 h
      change F.residueMap ((a : F.valuationSubring) - 1) = 0 at hz
      simpa only [map_sub, map_one, sub_eq_zero] using hz
  exact QuotientGroup.liftEquiv (higherPrincipalUnitGroup F 1)
    (by
      simpa only [residueUnitHom] using
        (IsLocalRing.surjective_units_map_of_local_ringHom
          F.residueMap IsLocalRing.residue_surjective
          (inferInstanceAs (IsLocalHom F.residueMap))))
    hk.symm

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
