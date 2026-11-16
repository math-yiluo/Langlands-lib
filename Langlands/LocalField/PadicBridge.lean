import Langlands.LocalField.Canonical
import Langlands.LocalField.PadicResidueNormalization
import Langlands.AllField.Representation.RankinSelberg.LocalFieldUnequalRankFunctionalEquationReduction
import Langlands.Representation.Conductor.UnramifiedPrincipalSeries

/-!
# The canonical p-adic specialization of general local-field data

`TopologicalData.toLocalFieldData` forgets the specified p-adic base extension.
The `Langlands.PadicField.CanonicalLocalField` scope supplies the canonical
topology, valuation, local-field certificate and Borel structures together.
Arithmetic comparisons are definitional; explicit absolute-value inputs are
identified by the published general-field normalization theorem.
-/

noncomputable section

namespace Langlands.PadicField

universe u
variable {p : ℕ} [Fact p.Prime]

namespace TopologicalData

variable {F : PadicField.{u} p} (T : F.TopologicalData)

/-- Forget the p-adic base extension, retaining exactly the supplied topology
and valuation. -/
def toLocalFieldData : LocalFieldData F.Carrier where
  topology := T.topology
  valuativeRel := T.valuativeRel
  localField := T.localField

@[simp] theorem toLocalFieldData_residueCardinality :
    T.toLocalFieldData.residueCardinality = T.residueCardinality := rfl

@[simp] theorem toLocalFieldData_discreteValuation :
    T.toLocalFieldData.discreteValuation = T.discreteValuation := rfl

@[simp] theorem toLocalFieldData_uniformizer :
    T.toLocalFieldData.uniformizer = T.uniformizer := rfl

@[simp] theorem toLocalFieldData_ord (x : F.Carrier) :
    T.toLocalFieldData.ord x = T.ord x := rfl

@[simp] theorem toLocalFieldData_normalizedAbs (x : F.Carrier) :
    T.toLocalFieldData.normalizedAbs x = T.normalizedAbs x := rfl

/-- The bundled absolute value used by the all-field port has the supplied
p-adic residue normalization. -/
@[simp] theorem toLocalFieldData_normalizedAbsoluteValue (x : F.Carrier) :
    AllField.RankinSelberg.normalizedAbsoluteValue T.toLocalFieldData x =
      T.normalizedAbs x := rfl

end TopologicalData

/-- The canonical supplied general local-field data of a p-adic field. -/
def canonicalLocalFieldData (F : PadicField.{u} p) : LocalFieldData F.Carrier :=
  F.canonicalTopologicalData.toLocalFieldData

namespace CanonicalLocalField

variable (F : PadicField.{u} p)

scoped instance topology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

scoped instance valuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel

scoped instance localField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

scoped instance valuativeExtension : ValuativeExtension (Padic p) F.Carrier :=
  F.canonicalTopologicalData.valuativeExtension

scoped instance moduleTopology : IsModuleTopology (Padic p) F.Carrier :=
  F.canonicalTopologicalData.moduleTopology

scoped instance t2Space : T2Space F.Carrier :=
  HarmonicAnalysis.GeneralLocalField.t2Space F.Carrier

scoped instance totallyDisconnectedSpace : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier using 1
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation F.Carrier)
  infer_instance

scoped instance measurableSpace : MeasurableSpace F.Carrier := borel F.Carrier

scoped instance borelSpace : BorelSpace F.Carrier := ⟨rfl⟩

end CanonicalLocalField

open scoped CanonicalLocalField

variable (F : PadicField.{u} p)

@[simp] theorem ofInstances_eq_canonicalLocalFieldData :
    LocalFieldData.ofInstances F.Carrier = F.canonicalLocalFieldData := rfl

/-- The canonical residue cardinality satisfies the explicit general-statement
input predicate. -/
theorem canonical_isResidueCardinality :
    Conductor.UnramifiedPrincipalSeries.IsResidueCardinality (F := F.Carrier)
      F.canonicalTopologicalData.residueCardinality := rfl

/-- The explicit cardinality input is the cardinality of the canonical data. -/
theorem eq_canonical_residueCardinality (q : ℕ)
    (hq : Conductor.UnramifiedPrincipalSeries.IsResidueCardinality
      (F := F.Carrier) q) :
    q = F.canonicalTopologicalData.residueCardinality := hq

/-- Reuse the general normalization comparison for any explicitly supplied
uniformizing unit and absolute value on the canonical p-adic field. -/
theorem eq_canonical_normalizedAbsoluteValue (q : ℕ)
    (hq : Conductor.UnramifiedPrincipalSeries.IsResidueCardinality
      (F := F.Carrier) q)
    (abv : AbsoluteValue F.Carrier ℝ) (ϖ : F.Carrierˣ)
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement
      (ValuativeRel.valuation F.Carrier) ϖ)
    (habv : abv (ϖ : F.Carrier) = (q : ℝ)⁻¹)
    (hunit : ∀ x : F.Carrier, ValuativeRel.valuation F.Carrier x = 1 →
      abv x = 1) :
    abv = AllField.RankinSelberg.normalizedAbsoluteValue F.canonicalLocalFieldData :=
  AllField.RankinSelberg.eq_normalizedAbsoluteValue_ofInstances q hq abv ϖ hϖ habv hunit

theorem explicit_abv_eq_canonical_normalizedAbs (q : ℕ)
    (hq : Conductor.UnramifiedPrincipalSeries.IsResidueCardinality
      (F := F.Carrier) q)
    (abv : AbsoluteValue F.Carrier ℝ) (ϖ : F.Carrierˣ)
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement
      (ValuativeRel.valuation F.Carrier) ϖ)
    (habv : abv (ϖ : F.Carrier) = (q : ℝ)⁻¹)
    (hunit : ∀ x : F.Carrier, ValuativeRel.valuation F.Carrier x = 1 →
      abv x = 1) (x : F.Carrier) :
    abv x = F.canonicalTopologicalData.normalizedAbs x := by
  rw [F.eq_canonical_normalizedAbsoluteValue q hq abv ϖ hϖ habv hunit]
  rfl

end Langlands.PadicField
