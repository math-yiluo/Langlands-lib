import Langlands.Representation.Classification.RelativeCosocleAdmissibilityStatement
import Langlands.Representation.Classification.FineTwistRegularityProof
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof

/-! # Admissibility for the actual relative cosocle inputs -/

noncomputable section

namespace Langlands

open GeneralLinear RelativeRegularComparison

universe uF uV uW

namespace RelativeRegularComparison

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {T : F.TopologicalData} {n : ℕ} {B : BlockShape n}
  {π : Rep.{uV} ℂ (B.Levi F.Carrier)}

/-- The universal-Haar tempered predicate is nonvacuous and implies
admissibility for the supplied product-Levi topology. -/
theorem IsLeviTempered.isAdmissible (h : IsLeviTempered T B π) :
    letI := T.topology
    IsAdmissible π.ρ := by
  let := T.topology
  let := T.leviTopologicalGroup B
  let Z := B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)
  let := borel Z
  have : BorelSpace Z := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_leviCentralQuotient B
  exact (h μ).1

/-- The same Haar-existence argument extracts admissibility from analytic
square-integrability on the product Levi. -/
theorem IsLeviSquareIntegrable.isAdmissible (h : IsLeviSquareIntegrable T B π) :
    letI := T.topology
    IsAdmissible π.ρ := by
  let := T.topology
  let := T.leviTopologicalGroup B
  let Z := B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)
  let := borel Z
  have : BorelSpace Z := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_leviCentralQuotient B
  exact (h μ).1

end RelativeRegularComparison

/-- Analytic Levi inputs and all actual twisted outer quotients are admissible,
with independent field, Levi-carrier and target-carrier universes. -/
theorem relativeCosocleAdmissibility :
    RelativeCosocleAdmissibilityStatement.{uF, uV, uW} := by
  intro p _ F T
  let := T.topology
  intro n B π
  refine ⟨fun h => h.isAdmissible, fun h => h.isAdmissible, ?_⟩
  intro hπ t
  have hπt : IsAdmissible (T.leviRealPowerTwist B t π.ρ) :=
    (T.isAdmissible_leviRealPowerTwist_iff B t π.ρ).mpr hπ
  have hI : IsAdmissible (T.normalizedParabolicInduced B
      (T.leviRealPowerTwist B t π.ρ)) :=
    Parabolic.normalizedInductionAdmissibility F T B _
      (T.leviRealPowerTwist B t π.ρ) hπt
  refine ⟨hπt, hI, ?_⟩
  intro J q hq
  let := T.generalLinearTopologicalGroup n
  apply Unramified.SphericalExistence.isAdmissible_of_surjective ?_ q hq hI
  intro H
  obtain ⟨K, hK, hKH, -⟩ :=
    B.exists_compactOpenSubgroup_hasBlockIwahoriFactorization T
      (H.isOpen.mem_nhds H.one_mem)
  exact ⟨K, hK, hKH⟩

end Langlands
