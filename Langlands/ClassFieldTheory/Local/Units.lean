import Langlands.LocalField.Normalization.Definitions
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# Multiplicative and unit objects of an actual p-adic field

All objects use the specified `PadicField.TopologicalData`. The field's
multiplicative group is `F.Carrierˣ`, with Mathlib's units topology, and the
integer and residue rings are the accepted normalization constructions.
No reciprocity map or class-field-theoretic assertion is assumed.
-/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- The units topology on the actual multiplicative group of the field.
It is explicit so two supplied local-field realizations cannot be confused. -/
abbrev multiplicativeTopology : TopologicalSpace F.Carrierˣ :=
  letI := T.topology
  inferInstance

/-- The same accepted integer ring, viewed through Mathlib's valuation-subring API. -/
abbrev valuationRing : ValuationSubring F.Carrier :=
  letI := T.valuativeRel
  (ValuativeRel.valuation F.Carrier).valuationSubring

/-- Valuation-zero elements of the actual field multiplicative group. -/
abbrev unitSubgroup : Subgroup F.Carrierˣ :=
  T.valuationRing.unitGroup

/-- Principal units, using Mathlib's actual valuation-subring construction. -/
abbrev principalUnitSubgroup : Subgroup F.Carrierˣ :=
  T.valuationRing.principalUnitGroup

/-- The valuation-zero subgroup and the units of the accepted integer ring
are canonically the same group. -/
abbrev integerUnitsEquiv : T.unitSubgroup ≃* T.Integersˣ :=
  T.valuationRing.unitGroupMulEquiv

/-- Inclusion of the integer-ring units in the field multiplicative group. -/
def integerUnitsInclusion : T.Integersˣ →* F.Carrierˣ :=
  Units.map T.Integers.subtype.toMonoidHom

/-- The same inclusion with its intrinsic continuity certificate. -/
def integerUnitsInclusionContinuous :
    letI := T.topology
    T.Integersˣ →ₜ* F.Carrierˣ :=
  letI := T.topology
  { T.integerUnitsInclusion with
    continuous_toFun := continuous_subtype_val.units_map _ }

/-- Reduction of actual integer units to actual residue-field units. -/
def residueUnits : T.Integersˣ →* T.ResidueFieldˣ :=
  Units.map T.residue.toMonoidHom

/-- Principal units identified with the kernel of reduction. -/
abbrev principalUnitsEquiv :
    T.principalUnitSubgroup ≃* T.residueUnits.ker :=
  T.valuationRing.principalUnitGroupEquiv

/-- The quotient integer ring modulo the `n`th power of its maximal ideal.
At `n = 0` this is the zero ring. -/
abbrev TruncatedIntegers (n : ℕ) :=
  T.Integers ⧸ (IsLocalRing.maximalIdeal T.Integers) ^ n

/-- Actual reduction modulo a power of the maximal ideal. -/
def truncatedReduction (n : ℕ) : T.Integers →+* T.TruncatedIntegers n :=
  Ideal.Quotient.mk _

/-- Reduction of integer units modulo a power of the maximal ideal. -/
def truncatedUnitsReduction (n : ℕ) : T.Integersˣ →* (T.TruncatedIntegers n)ˣ :=
  Units.map (T.truncatedReduction n).toMonoidHom

/-- Reduction on units is continuous for the quotient-ring topology. -/
def truncatedUnitsReductionContinuous (n : ℕ) :
    letI := T.topology
    T.Integersˣ →ₜ* (T.TruncatedIntegers n)ˣ :=
  letI := T.topology
  { T.truncatedUnitsReduction n with
    continuous_toFun := (show Continuous (T.truncatedReduction n) from
      continuous_quot_mk).units_map _ }

/-- Congruence units in the actual integer-ring unit group.
This is `1 + m^n` for positive `n`; at zero it is the full unit group. -/
def congruenceUnits (n : ℕ) : Subgroup T.Integersˣ :=
  (T.truncatedUnitsReduction n).ker

/-- The same congruence units as an actual subgroup of `Fˣ`.
The map is the canonical inclusion, not a choice of representatives. -/
def unitFiltration (n : ℕ) : Subgroup F.Carrierˣ :=
  (T.congruenceUnits n).map T.integerUnitsInclusion

/-- The unit quotient with its ordinary quotient-group topology when
`T.topology` is installed. No discrete topology is substituted. -/
abbrev UnitQuotient (n : ℕ) := T.Integersˣ ⧸ T.congruenceUnits n

/-- Canonical projection to the unit quotient. -/
def unitQuotientProjection (n : ℕ) : T.Integersˣ →* T.UnitQuotient n :=
  QuotientGroup.mk' _

/-- The reduction map induced on the actual quotient by its kernel. -/
def unitQuotientReduction (n : ℕ) :
    T.UnitQuotient n →* (T.TruncatedIntegers n)ˣ :=
  QuotientGroup.lift _ (T.truncatedUnitsReduction n) (fun _ h => h)

/-- Continuous projection with the quotient topology, without an openness assumption. -/
def unitQuotientProjectionContinuous (n : ℕ) :
    letI := T.topology
    T.Integersˣ →ₜ* T.UnitQuotient n :=
  letI := T.topology
  { T.unitQuotientProjection n with
    continuous_toFun := QuotientGroup.continuous_mk }

/-- Continuity of the induced reduction follows from the quotient topology. -/
def unitQuotientReductionContinuous (n : ℕ) :
    letI := T.topology
    T.UnitQuotient n →ₜ* (T.TruncatedIntegers n)ˣ :=
  letI := T.topology
  { T.unitQuotientReduction n with
    continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
      (T.truncatedUnitsReductionContinuous n).continuous }

/-- Multiplicative notation for the additive normalized order on nonzero elements.
The zero convention of `ord` causes no issue because the input is a unit. -/
def orderHom : F.Carrierˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (T.ord x)
  map_one' := by
    change Multiplicative.ofAdd (-WithZero.log (T.discreteValuation 1)) = 1
    simp
  map_mul' x y := by
    change Multiplicative.ofAdd (-WithZero.log (T.discreteValuation ((x : F.Carrier) * y))) =
      Multiplicative.ofAdd (-WithZero.log (T.discreteValuation x)) *
        Multiplicative.ofAdd (-WithZero.log (T.discreteValuation y))
    rw [map_mul, WithZero.log_mul
      ((T.discreteValuation).ne_zero_iff.mpr x.ne_zero)
      ((T.discreteValuation).ne_zero_iff.mpr y.ne_zero), neg_add]
    rfl

/-- The actual quotient of the multiplicative group by its valuation-zero units.
This construction does not assert an isomorphism with the integers. -/
abbrev ValuationQuotient := F.Carrierˣ ⧸ T.unitSubgroup

/-- Canonical projection to the multiplicative valuation quotient. -/
def valuationQuotientProjection : F.Carrierˣ →* T.ValuationQuotient :=
  QuotientGroup.mk' _

/-- The multiplicative valuation quotient has its actual quotient topology. -/
def valuationQuotientProjectionContinuous :
    letI := T.topology
    F.Carrierˣ →ₜ* T.ValuationQuotient :=
  letI := T.topology
  { T.valuationQuotientProjection with
    continuous_toFun := QuotientGroup.continuous_mk }

end Langlands.PadicField.TopologicalData
