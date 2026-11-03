import Langlands.Galois.Local.SeparableInertiaDefinitions
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian

noncomputable section

open IsLocalRing ValuativeRel
open scoped NNReal

namespace Langlands.LocalGalois.Separable

universe u

section Arithmetic

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance : NontriviallyNormedField F := localNormedField F
local instance : IsUltrametricDist F := localNormedField_ultrametric F
local instance : CompleteSpace F := localNormedField_complete F
local instance : Finite (ResidueField (baseIntegers F)) := localResidue_finite F

/-- The actual residue field is an algebraic closure for the algebra induced by
the published residue map. -/
def FixedFieldResidueIsAlgClosure : Prop :=
  letI := (residueToFixedField F).toAlgebra
  IsAlgClosure 𝓀[F] (ResidueField (fixedFieldIntegers F))

/-- Every value of the actual restricted spectral valuation, including zero,
is attained by the chosen base norm in the same codomain. -/
def FixedFieldValuesFromBase : Prop :=
  ∀ x : inertiaFixedField F, ∃ a : F, fixedFieldValuation F x = ‖a‖₊

/-- The canonical valuation of the relation induced by `fixedFieldValued` has
exactly the published actual integer ring. This comparison uses no arithmetic
property of the inertia fixed field. -/
theorem fixedFieldIntrinsicIntegers_eq :
    letI := ValuativeRel.ofValuation (fixedFieldValued F).v
    (valuation (inertiaFixedField F)).valuationSubring = fixedFieldIntegers F := by
  let := ValuativeRel.ofValuation (fixedFieldValued F).v
  let : Valuation.Compatible (fixedFieldValued F).v :=
    Valuation.Compatible.ofValuation _
  exact (Valuation.isEquiv_iff_valuationSubring _ _).mp
    (ValuativeRel.isEquiv (valuation (inertiaFixedField F)) (fixedFieldValued F).v)

/-- Discreteness of the intrinsic value group of the explicitly induced
valuation relation, with no discreteness claim about `NNReal`. -/
def FixedFieldIntrinsicDiscrete : Prop :=
  letI := ValuativeRel.ofValuation (fixedFieldValued F).v
  ValuativeRel.IsDiscrete (inertiaFixedField F)

/-- The published actual integer ring is a discrete valuation ring. -/
def FixedFieldIntegersIsDVR : Prop :=
  IsDiscreteValuationRing (fixedFieldIntegers F)

/-- The published actual integer ring is Henselian. -/
def FixedFieldIntegersIsHenselian : Prop :=
  HenselianLocalRing (fixedFieldIntegers F)

end Arithmetic

/-- Characteristic-uniform residue, value and integer-ring arithmetic targets
for the actual separable inertia fixed field. -/
def SeparableUnramifiedArithmeticStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F],
      FixedFieldResidueIsAlgClosure F ∧ FixedFieldValuesFromBase F ∧
        FixedFieldIntrinsicDiscrete F ∧ FixedFieldIntegersIsDVR F ∧
          FixedFieldIntegersIsHenselian F

end Langlands.LocalGalois.Separable
