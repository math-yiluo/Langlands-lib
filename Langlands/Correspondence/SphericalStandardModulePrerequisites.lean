import Langlands.Correspondence.SphericalStandardLPrerequisites

/-! # Two independent ordered principal-series obligations -/

noncomputable section

namespace Langlands.Correspondence

universe uF uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance modulePrerequisiteFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance modulePrerequisiteGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- A subrepresentation of a principal series in Langlands order that contains
a nonzero spherical vector is the whole principal series. -/
def OrderedUnramifiedSphericalGenerationStatement : Prop :=
  ∀ (r : ℕ) (z : Fin (r + 1) → ℂˣ),
    Monotone (fun i => ‖(z i : ℂ)‖) →
      ∀ S : Subrepresentation (Unramified.principalSeriesOfTuple F z),
        fixedVectors S.toRepresentation (sphericalSubgroup F r) ≠ ⊥ →
          S = ⊤

/-- Grouping equal-norm characters gives a tempered datum whose actual standard
module is the given ordered principal series. No quotient is prescribed. -/
def OrderedUnramifiedTemperedRealizationStatement : Prop :=
  ∀ (r : ℕ) (z : Fin (r + 1) → ℂˣ),
    Monotone (fun i => ‖(z i : ℂ)‖) →
      ∃ d : PadicField.TopologicalData.TemperedLanglandsDatum.{uA, uF}
          F.canonicalTopologicalData (r + 1),
        Nonempty (d.standardModule.representation.Equiv
          (Unramified.principalSeriesOfTuple F z))

/-- The representation-theoretic obligations used by the conditional reduction
to the spherical standard-module presentation. -/
def SphericalStandardModulePrerequisitesStatement : Prop :=
  OrderedUnramifiedSphericalGenerationStatement F ∧
    OrderedUnramifiedTemperedRealizationStatement.{uF, uA} F

end Langlands.Correspondence
