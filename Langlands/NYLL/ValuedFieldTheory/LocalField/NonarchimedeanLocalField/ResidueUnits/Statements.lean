/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Adapted by Worker 126 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709,
-- ResidueUnits.lean, lines 105-111, 140-146, 149-153, 165-168 and 208-210
-- (M137.012, .016-.018, .022):
-- each theorem statement is a Prop-valued definition; the source proofs are omitted.
-- See Statements.md for the exact source lines, modifications and licenses/NYLL/.

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueUnits.Definitions

/-!
# Residue units and integer units modulo first principal units: statement targets

Proposition targets for elimination of a class of `𝒪[K]ˣ ⧸ U¹` through the class map, the
underlying residue of a reduced unit, the kernel criterion for reduction, the equality of the
first principal units with the kernel of reduction, and surjectivity of reduction.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

set_option linter.unusedVariables false in
/-- Eliminate a quotient class through the canonical class map. -/
protected def IntegerUnitsModPrincipalUnits.inductionOnStatement
    {K : Type u} [Field K] [ValuativeRel K]
    {motive : IntegerUnitsModPrincipalUnits K → Prop}
    (q : IntegerUnitsModPrincipalUnits K)
    (h : ∀ x : 𝒪[K]ˣ, motive (integerUnitsModPrincipalUnitsMk K x)) : Prop :=
  motive q

/-- Reduction of a valuation-ring unit has underlying residue equal to reduction of its underlying
integer. -/
def integerUnitsToResidueUnits_applyStatement (K : Type u) [Field K] [ValuativeRel K]
    (x : 𝒪[K]ˣ) : Prop :=
  ((residueUnitsConcreteEquiv K (integerUnitsToResidueUnits K x) : 𝓀[K]ˣ) :
        𝓀[K]) =
      IsLocalRing.residue 𝒪[K] (x : 𝒪[K])

/-- Kernel criterion for reduction on valuation-integer units. -/
def mem_ker_integerUnitsToResidueUnits_iffStatement (K : Type u) [Field K] [ValuativeRel K]
    (x : 𝒪[K]ˣ) : Prop :=
  x ∈ (integerUnitsToResidueUnits K).ker ↔
      IsLocalRing.residue 𝒪[K] (x : 𝒪[K]) = 1

/-- The first principal-unit group is the kernel of reduction to residue-field units. -/
def principalUnits_one_eq_ker_integerUnitsToResidueUnitsStatement
    (K : Type u) [Field K] [ValuativeRel K] : Prop :=
  principalUnits K 1 = (integerUnitsToResidueUnits K).ker

/-- Every residue-field unit lifts to a valuation-ring unit. -/
def integerUnitsToResidueUnits_surjectiveStatement (K : Type u) [Field K] [ValuativeRel K] :
    Prop :=
  Function.Surjective (integerUnitsToResidueUnits K)

end

end Langlands.NYLL.LocalFieldTheory
