import Langlands.Representation.Classification.DiscreteSeriesPositiveRootSupportStatement
import Langlands.Representation.Classification.FineTwistRegularityProof
import Langlands.Representation.CuspidalSupport.LeviCuspidalQuotientProof
import Langlands.Representation.Exponents.PositiveRootParameterConeProof
import Langlands.Representation.Exponents.UnitaryFineTwistScalarCharacterProof
import Langlands.Group.GL.CentralQuotientTopologyProof
import Langlands.Representation.Unitary.LeviCuspidalRealUnitarizationProof
import Langlands.Representation.Exponents.RefinedQuotientOppositeCharacterProof
import Langlands.Representation.Exponents.RefinedOppositeSquareIntegrableConeProof

/-!
# Positive-root unitary cuspidal support of product-Levi discrete series

Extract an actual cuspidal upper quotient, unitarize its datum, and apply the
strict opposite-Jacquet exponent theorem to the same quotient. The resulting
weighted scalar cone is exactly the required strict root-parameter cone.
-/

noncomputable section

namespace Langlands.DiscreteSeriesPositiveRootSupport

open GeneralLinear Geometric RelativeJacquetMultiplicity RelativeRegularComparison

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (D : BlockShape n)

-- The analytic predicate has a nonvacuous Haar specialization giving admissibility.
private theorem squareIntegrable_admissible (σ : Rep.{uV} ℂ (D.Levi F.Carrier))
    (hsq : IsLeviSquareIntegrable T D σ) :
    letI := T.topology
    IsAdmissible σ.ρ := by
  let := T.topology
  let := T.leviTopologicalGroup D
  let Z := D.Levi F.Carrier ⧸ Subgroup.center (D.Levi F.Carrier)
  let : MeasurableSpace Z := borel Z
  let : BorelSpace Z := ⟨rfl⟩
  obtain ⟨_, _, _, _, hhaar⟩ := (glBlockCentralQuotientTopology p F T n).2 D
  obtain ⟨μ, hμ⟩ := hhaar.1
  let := hμ
  exact (hsq μ).1

-- On the original inducing carrier, the negative fine twist cancels +t.
private theorem fineTwist_unitarizing_cancel (R : BlockRefinement D)
    (τ : Rep.{max uF uV} ℂ ((D.flatten R).Levi F.Carrier))
    (t : Fin (D.flatten R).length → ℝ) :
    fineTwist T D R (Rep.of (T.leviRealPowerTwist (D.flatten R) t τ.ρ)) t 0 =
      fineTwist T D R τ 0 0 := by
  unfold fineTwist
  congr 1
  change
    (T.leviRealPowerTwist (D.flatten R)
      (fun k => -t k + (0 : Fin D.length → ℝ) ((D.flattenBlockEquiv R).symm k).1)
      (T.leviRealPowerTwist (D.flatten R) t τ.ρ)).comp _ =
    (T.leviRealPowerTwist (D.flatten R)
      (fun k => -(0 : Fin (D.flatten R).length → ℝ) k +
        (0 : Fin D.length → ℝ) ((D.flattenBlockEquiv R).symm k).1) τ.ρ).comp _
  simp only [Pi.zero_apply, add_zero, neg_zero]
  change
    (T.leviRealPowerTwist (D.flatten R) (-t)
      (T.leviRealPowerTwist (D.flatten R) t τ.ρ)).comp _ =
    (T.leviRealPowerTwist (D.flatten R) 0 τ.ρ).comp _
  rw [T.leviRealPowerTwist_neg_cancel, T.leviRealPowerTwist_zero]

end Langlands.DiscreteSeriesPositiveRootSupport

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity RelativeRegularComparison

universe uF uV

/-- Every irreducible analytically square-integrable product-Levi representation
is an actual upper induced quotient of unitary cuspidal data at the negative
of the specified strict positive-root parameter. -/
theorem glDiscreteSeriesPositiveRootSupport :
    GLDiscreteSeriesPositiveRootSupportStatement.{uF, uV} := by
  intro p hp F T
  let := T.topology
  intro n hn D σ hσirr hσsq
  let := hσirr
  have hσnt : Nontrivial σ.V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (D.Levi F.Carrier)) σ.ρ.asModule
  have hσadm : IsAdmissible σ.ρ := DiscreteSeriesPositiveRootSupport.squareIntegrable_admissible T D σ hσsq
  obtain ⟨R, τ, hirr, hcusp, q, hq⟩ :=
    CuspidalSupport.leviCuspidalQuotientTheorem p F T n hn D σ hσirr hσadm
  obtain ⟨t, hunit⟩ :=
    leviCuspidalRealUnitarization p F T n hn (D.flatten R) τ.V τ.ρ hirr hcusp
  let ω : Rep.{max uF uV} ℂ ((D.flatten R).Levi F.Carrier) :=
    Rep.of (T.leviRealPowerTwist (D.flatten R) t τ.ρ)
  have hωirr : Representation.IsIrreducible ω.ρ :=
    (T.isIrreducible_leviRealPowerTwist_iff (D.flatten R) t τ.ρ).mpr hirr
  have hωcusp : CuspidalSupport.IsLeviCuspidal (D.flatten R) ω.ρ :=
    (T.isLeviCuspidal_leviRealPowerTwist_iff (D.flatten R) t τ.ρ).mpr hcusp
  have hfine : fineTwist T D R ω t 0 = fineTwist T D R τ 0 0 :=
    DiscreteSeriesPositiveRootSupport.fineTwist_unitarizing_cancel T D R τ t
  have hsourceadm : IsAdmissible (fineTwist T D R ω t 0).ρ :=
    (fineTwistIrreducibleAdmissible p F T n D R ω hωirr hωcusp t 0).2.1
  obtain ⟨χ, hχopen, hχscalar, hχreal⟩ :=
    Exponents.unitaryFineTwistScalarCharacter p F T n D R ω hωirr hωcusp.1 hunit t
  have hquot : ∃ q' :
      (innerInduced T D R (fineTwist T D R ω t 0)).ρ.IntertwiningMap σ.ρ,
      Function.Surjective q' := by
    rw [hfine]
    exact ⟨q, hq⟩
  have hocc := Exponents.refinedQuotientOppositeCharacter p F T n hn D R
    (fineTwist T D R ω t 0) σ hsourceadm hσadm hσnt χ hχscalar hquot
  have hcone := Exponents.refinedOppositeSquareIntegrableCone p F T n hn D σ
    hσirr hσsq R χ hχopen hocc.2 _ hχreal
  have hparam : IsPositiveRootParameter D R t := by
    apply (Exponents.positiveRootParameterCone n D R t).mpr
    intro i
    simpa only [neg_mul, neg_neg, D.flatten_size_flattenBlockEquiv R] using hcone i
  exact ⟨R, ω, t, hωirr, hωcusp, hunit, hparam, hquot⟩


end Langlands
