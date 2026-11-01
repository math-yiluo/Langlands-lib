import Langlands.Representation.RankinSelberg.AdjacentRankSectionSurjectivity
import Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof
import Langlands.Representation.Induction.CompactQuotientProof
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Admissibility of the actual adjacent induction and closed fixed coefficients. -/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis

universe uF uV uG

section Projection

variable {K : Type uF} [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] {r : ℕ}

theorem continuous_adjacentRankLowerLargeProjection :
    Continuous (adjacentRankLowerLargeProjection (K := K) (r := r)) :=
  (continuous_apply 0).comp
    ((adjacentRankLowerShape r).oppositeLeviProjectionContinuous K).continuous

theorem isOpenMap_adjacentRankLowerLargeProjection :
    IsOpenMap (adjacentRankLowerLargeProjection (K := K) (r := r)) :=
  (isOpenMap_eval 0).comp
    (isOpenMap_snd.comp
      ((adjacentRankLowerShape r).oppositeDecompositionHomeomorph K).isOpenMap)

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] in
theorem adjacentRankLowerLargeProjection_surjective :
    Function.Surjective (adjacentRankLowerLargeProjection (K := K) (r := r)) := by
  intro h
  let m : (adjacentRankLowerShape r).Levi K := Function.update 1 0 h
  refine ⟨(adjacentRankLowerShape r).oppositeLeviInParabolic K m, ?_⟩
  change (adjacentRankLowerShape r).oppositeLeviProjection K
    ((adjacentRankLowerShape r).oppositeLeviInParabolic K m) 0 = h
  rw [(adjacentRankLowerShape r).oppositeLeviProjection_section]
  exact Function.update_self _ _ _

end Projection

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance adjacentAdmissibilityTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance adjacentAdmissibilityValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance adjacentAdmissibilityLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance adjacentAdmissibilityT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (χ : Quasicharacter F.Carrier)

/-- Admissibility of the original representation implies admissibility of the
actual normalized lower-parabolic inducing action on its exact tensor carrier. -/
theorem adjacentRankLowerTensorRepresentation_isAdmissible (hσ : IsAdmissible σ) :
    IsAdmissible (adjacentRankLowerTensorRepresentation F σ χ) := by
  let P := (adjacentRankLowerShape r).oppositeParabolic F.Carrier
  let a := adjacentRankLowerLargeProjection (K := F.Carrier) (r := r)
  let ξ := adjacentRankDeterminantWeight F.canonicalTopologicalData χ
    (r + 1) ((r + 2 : ℕ) / 2)
  let θ := adjacentRankDeterminantWeight F.canonicalTopologicalData χ
    (r + 2) ((r + 1 : ℕ) / 2)
  have ha : Continuous a := continuous_adjacentRankLowerLargeProjection
  have hcomp : IsAdmissible (σ.comp a) :=
    (isAdmissible_comp_iff_of_open_surjective σ a ha
      isOpenMap_adjacentRankLowerLargeProjection
      adjacentRankLowerLargeProjection_surjective).mpr hσ
  let φ₁ : P →* ℂˣ := θ.toMonoidHom.comp P.subtype
  let φ₂ : P →* ℂˣ := ξ.toMonoidHom.comp a
  have h₁ : IsOpen (φ₁.ker : Set P) := by
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact θ.isOpen_ker.preimage continuous_subtype_val
  have h₂ : IsOpen (φ₂.ker : Set P) := by
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact ξ.isOpen_ker.preimage ha
  have hker : IsOpen ((φ₁ * φ₂⁻¹).ker : Set P) := by
    refine Subgroup.isOpen_mono (H₁ := φ₁.ker ⊓ φ₂.ker) ?_ ?_
    · intro q hq
      change φ₁ q * (φ₂ q)⁻¹ = 1
      rw [show φ₁ q = 1 from hq.1, show φ₂ q = 1 from hq.2]
      simp
    · exact h₁.inter h₂
  have hc : IsAdmissible (adjacentRankLowerCompactRepresentation F σ χ) :=
    (isAdmissible_twist_iff (φ₁ * φ₂⁻¹) (σ.comp a) hker).mpr hcomp
  exact isAdmissible_of_equiv (adjacentRankLowerInducingCoordinates F σ χ).symm hc

/-- The exact canonical normalized opposite induction on the original tensor
carrier is admissible for every continuous quasicharacter. -/
theorem adjacentRankNormalizedInduced_isAdmissible (hσ : IsAdmissible σ) :
    IsAdmissible
      (F.canonicalNormalizedOppositeParabolicInduced (adjacentRankLowerShape r)
        ((adjacentRankLowerShape r).blockTensor
          (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)))) := by
  let := oppositeParabolicQuotientCompact F F.canonicalTopologicalData
    (adjacentRankLowerShape r)
  exact Induction.smoothInduced_isAdmissible_of_compactSpace _
    (adjacentRankLowerTensorRepresentation F σ χ)
    (adjacentRankLowerTensorRepresentation_isAdmissible F σ χ hσ)

end Padic

section Coefficients

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (ℓ : V →ₗ[ℂ] ℂ) (J : OpenSubgroup G)

/-- Coefficients of vectors fixed by one open subgroup, with product topology
only on the target function space. The source needs no topology. -/
def fixedCoefficientMap : fixedVectors ρ J.toSubgroup →ₗ[ℂ] (G → ℂ) where
  toFun v g := ℓ (ρ g v.val)
  map_add' v w := by ext g; simp
  map_smul' c v := by ext g; simp

@[simp] theorem fixedCoefficientMap_apply (v : fixedVectors ρ J.toSubgroup) (g : G) :
    fixedCoefficientMap ρ ℓ J v g = ℓ (ρ g v.val) := rfl

/-- Admissibility makes the fixed-vector coefficient image finite dimensional
and hence closed for pointwise convergence, without injectivity of coefficients. -/
theorem isClosed_range_fixedCoefficientMap (hρ : IsAdmissible ρ) :
    IsClosed (Set.range (fixedCoefficientMap ρ ℓ J)) := by
  let := hρ.2 J
  exact (fixedCoefficientMap ρ ℓ J).range.closed_of_finiteDimensional

/-- Pointwise limits of coefficients of vectors fixed by the same open subgroup
remain coefficients of vectors fixed by that subgroup. -/
theorem mem_range_fixedCoefficientMap_of_tendsto (hρ : IsAdmissible ρ)
    (v : ℕ → fixedVectors ρ J.toSubgroup) (W : G → ℂ)
    (hv : ∀ g, Filter.Tendsto (fun n => ℓ (ρ g (v n).val))
      Filter.atTop (nhds (W g))) :
    W ∈ Set.range (fixedCoefficientMap ρ ℓ J) := by
  apply (isClosed_range_fixedCoefficientMap ρ ℓ J hρ).mem_of_tendsto
    (tendsto_pi_nhds.mpr hv)
  exact Filter.Eventually.of_forall fun n => ⟨v n, rfl⟩

end Coefficients

end Langlands.RankinSelberg
