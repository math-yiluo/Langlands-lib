import Langlands.Galois.Local.SeparableUnramifiedArithmeticStatement
import Mathlib.RingTheory.Valuation.Discrete.Basic

noncomputable section

open IsLocalRing ValuativeRel
open scoped NNReal

namespace Langlands.LocalGalois.Separable

universe u

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance separableValueArithmeticInstance1 : NontriviallyNormedField F := localNormedField F
local instance separableValueArithmeticInstance2 : IsUltrametricDist F := localNormedField_ultrametric F
local instance separableValueArithmeticInstance3 : CompleteSpace F := localNormedField_complete F

theorem fixedFieldValuation_base (a : F) :
    fixedFieldValuation F (algebraMap F (inertiaFixedField F) a) = ‖a‖₊ := by
  apply NNReal.eq
  exact spectralNorm_extends a

/-- Value attainment makes the canonical map from the base intrinsic value
group to that of the actual inertia fixed field an ordered isomorphism. -/
def fixedFieldValueGroupEquiv (h : FixedFieldValuesFromBase F) :
    letI := ValuativeRel.ofValuation (fixedFieldValued F).v
    ValueGroupWithZero F ≃*o ValueGroupWithZero (inertiaFixedField F) := by
  letI := ValuativeRel.ofValuation (fixedFieldValued F).v
  letI : Valuation.Compatible (fixedFieldValued F).v :=
    Valuation.Compatible.ofValuation _
  letI : ValuativeExtension F (inertiaFixedField F) :=
    ⟨fun a b => by
      rw [Valuation.vle_iff_le (fixedFieldValued F).v,
        Valuation.vle_iff_le (valuation F)]
      exact Valuation.HasExtension.val_map_le_iff
        (valuation F) (fixedFieldValuation F) a b⟩
  let f := ValuativeExtension.mapValueGroupWithZero F (inertiaFixedField F)
  have hf : StrictMono f := ValuativeExtension.mapValueGroupWithZero_strictMono
  have hs : Function.Surjective f := by
    intro γ
    obtain ⟨x, rfl⟩ := ValuativeRel.valuation_surjective γ
    obtain ⟨a, ha⟩ := h x
    refine ⟨valuation F a, ?_⟩
    rw [ValuativeExtension.mapValueGroupWithZero_valuation]
    apply (ValuativeRel.isEquiv (valuation (inertiaFixedField F))
      (fixedFieldValued F).v).eq_iff.mpr
    change fixedFieldValuation F (algebraMap F (inertiaFixedField F) a) =
      fixedFieldValuation F x
    rw [fixedFieldValuation_base, ha]
  exact { MulEquiv.ofBijective f.toMonoidHom ⟨hf.injective, hs⟩ with
    map_le_map_iff' := hf.le_iff_le }

theorem fixedFieldIntrinsicDiscrete_of_valuesFromBase (h : FixedFieldValuesFromBase F) :
    FixedFieldIntrinsicDiscrete F := by
  let := ValuativeRel.ofValuation (fixedFieldValued F).v
  let e := (fixedFieldValueGroupEquiv F h).symm.trans
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F)
  exact (ValuativeRel.nonempty_orderIso_withZeroMul_int_iff.mp ⟨e⟩).1

theorem fixedFieldIntegersIsDVR_of_valuesFromBase (h : FixedFieldValuesFromBase F) :
    FixedFieldIntegersIsDVR F := by
  let := ValuativeRel.ofValuation (fixedFieldValued F).v
  let : Valuation.Compatible (fixedFieldValued F).v :=
    Valuation.Compatible.ofValuation _
  let e := (fixedFieldValueGroupEquiv F h).trans
    (ValueGroupWithZero.orderMonoidIso (fixedFieldValued F).v)
  let e' := (Units.mapEquiv e.toMulEquiv).trans WithZero.unitsWithZeroEquiv
  let : IsCyclic (MonoidWithZeroHom.valueGroup
      (MonoidWithZeroHom.ofClass (fixedFieldValued F).v)) := e'.isCyclic.mp inferInstance
  let : Nontrivial (ValueGroupWithZero F)ˣ :=
    ValuativeRel.isNontrivial_iff_nontrivial_units.mp inferInstance
  let : Nontrivial (MonoidWithZeroHom.valueGroup
      (MonoidWithZeroHom.ofClass (fixedFieldValued F).v)) :=
    e'.symm.surjective.nontrivial
  exact Valuation.valuationSubring_isDiscreteValuationRing (fixedFieldValued F).v

end Langlands.LocalGalois.Separable
