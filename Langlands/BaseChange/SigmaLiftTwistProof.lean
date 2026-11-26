import Langlands.BaseChange.CyclicAlgebraDeterminant
import Langlands.BaseChange.SigmaLiftTwistStatement
import Langlands.BaseChange.WeightedConcordance
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.Topology.LocallyProfiniteProof

/-! # Compatibility of sigma-lifts with character twists -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis MeasureTheory

universe u v uV uW

private theorem continuous_algebraNorm {F : Type u} [Field F]
    [TopologicalSpace F] [IsTopologicalRing F] {E : Type v} [CommRing E] [Algebra F E]
    [Module.Finite F E] [TopologicalSpace E] [IsModuleTopology F E] :
    Continuous (Algebra.norm F : E → F) := by
  let b := Module.finBasis F E
  change Continuous (fun x : E => Algebra.norm F x)
  simp_rw [Algebra.norm_eq_matrix_det b]
  exact (IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap).matrix_det

private theorem locallyConstant_units_character {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ω : Fˣ →* ℂˣ)
    (hω : Continuous (fun z : Fˣ => (ω z : ℂ))) :
    IsLocallyConstant (fun z : Fˣ => (ω z : ℂ)) := by
  have := LocalFieldTopology.t2Space F
  have := LocalFieldTopology.units_locallyCompactSpace F
  have := LocalFieldTopology.units_totallyDisconnectedSpace F
  have : NonarchimedeanGroup Fˣ := by
    refine ⟨fun U hU => ?_⟩
    obtain ⟨H, _, hH⟩ := ((Langlands.Topology.LocallyProfiniteProof.vanDantzig _).mp
      Langlands.Topology.isLocallyProfinite_of_mathlib).2 U hU
    exact ⟨H, hH⟩
  exact RankinSelberg.isLocallyConstant_of_continuous_complex_character ω
    (Units.isEmbedding_val₀.continuous_iff.mpr hω)

private def weightTest {G : Type*} [TopologicalSpace G] (χ : G → ℂ)
    (hχ : IsLocallyConstant χ) (f : SchwartzBruhat G) : SchwartzBruhat G :=
  ⟨fun g => f g * χ g, f.locallyConstant.comp₂ hχ (· * ·), f.hasCompactSupport.mul_right⟩

private theorem twistedDistribution_twist_weight {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (χ : G →* ℂˣ) (hχ : IsLocallyConstant (fun g => (χ g : ℂ)))
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (hρ' : IsAdmissible (twist χ ρ))
    (A : Module.End ℂ V) (f : SchwartzBruhat G) :
    twistedDistribution μ (twist χ ρ) hρ' A f =
      twistedDistribution μ ρ hρ A (weightTest (fun g => (χ g : ℂ)) hχ f) := by
  let f' := weightTest (fun g => (χ g : ℂ)) hχ f
  have ha : Hecke.integratedAction μ (twist χ ρ) hρ'.1 f =
      Hecke.integratedAction μ ρ hρ.1 f' := by
    apply LinearMap.ext
    intro z
    rw [Hecke.integratedAction_apply, Hecke.integratedAction_apply]
    congr 1
    apply SimpleFunc.ext
    intro g
    simp only [Hecke.actionIntegrand_apply]
    change f g • ((χ g : ℂ) • ρ g z) = (f g * (χ g : ℂ)) • ρ g z
    rw [smul_smul]
  rw [twistedDistribution_apply, twistedDistribution_apply]
  apply congrArg FiniteRankEnd.trace
  apply Subtype.ext
  change (Character.finiteRankIntegratedAction μ (twist χ ρ) hρ' f).val.comp A =
    (Character.finiteRankIntegratedAction μ ρ hρ f').val.comp A
  rw [Character.finiteRankIntegratedAction_coe, Character.finiteRankIntegratedAction_coe, ha]

/-- Corresponding determinant twists preserve a local sigma-lift and its constant
when the supplied intertwiners have the same underlying operator. -/
theorem sigmaLiftTwist : SigmaLiftTwistStatement.{u, v, uV, uW} := by
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n hcyc
  let : Module.Finite F E := hcyc.1
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  have := generalLinear_t2Space_of_finite F E n
  have := generalLinear_locallyCompactSpace_of_finite F E n
  have := generalLinear_totallyDisconnectedSpace_of_finite F E n
  intro V _ _ W _ _ π hπ τ hτ A c ω hω
  dsimp only
  intro hπω hτω Aω hA hlift
  let χF : GeneralLinear n F →* ℂˣ := ω.comp determinant
  let ν : Eˣ →* Fˣ := Units.map (Algebra.norm F : E →* F)
  let χE : GeneralLinear n E →* ℂˣ := (ω.comp ν).comp determinant
  have hωlc := locallyConstant_units_character ω hω
  have hν : Continuous ν :=
    (continuous_algebraNorm (F := F) (E := E)).units_map (Algebra.norm F)
  have hχF : IsLocallyConstant (fun g => (χF g : ℂ)) :=
    hωlc.comp_continuous Matrix.GeneralLinearGroup.continuous_det
  have hχE : IsLocallyConstant (fun g => (χE g : ℂ)) :=
    hωlc.comp_continuous (hν.comp Matrix.GeneralLinearGroup.continuous_det)
  have hA' : Aω.toLinearMap = A.toLinearMap := LinearMap.ext (congrFun hA)
  refine ⟨hlift.1, ?_⟩
  let : MeasurableSpace (GeneralLinear n F) := borel _
  have : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear n E) := borel _
  have : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  intro μF _ μE _ φ f hcon
  let φ' := weightTest (fun g => (χE g : ℂ)) hχE φ
  let f' := weightTest (fun g => (χF g : ℂ)) hχF f
  have hcon' : AreConcordant σ l μF μE φ' f' :=
    hcon.mul_of_orbitValues (fun g => (χE g : ℂ)) (fun g => (χF g : ℂ))
      (fun γ _ x => by
        rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul])
      (fun δ γ hδγ _ x => by
        have hx : IsNormAssociated σ l (x⁻¹ * δ * entrywiseAut σ n x) γ := by
          simpa only [inv_one, one_mul, mul_one] using hδγ.twistedConj hcyc.pow_eq_one x 1
        exact congrArg (fun a : Fˣ => (ω a : ℂ)) (hx.norm_determinant_units_eq hcyc))
  change twistedDistribution μE (twist χE τ) hτω Aω.toLinearMap φ =
    c * Character.distribution μF (twist χF π) hπω f
  rw [hA', twistedDistribution_twist_weight μE χE hχE τ hτ hτω,
    ← twistedDistribution_one μF (twist χF π) hπω,
    twistedDistribution_twist_weight μF χF hχF π hπ hπω, twistedDistribution_one]
  exact hlift.2 μF μE φ' f' hcon'

end Langlands.BaseChange
