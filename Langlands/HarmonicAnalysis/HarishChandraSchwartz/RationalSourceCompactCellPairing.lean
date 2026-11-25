import Langlands.Representation.Plancherel.RationalSourceGammaGlobal
import Langlands.Representation.Plancherel.RationalSourceGammaIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! # Compact integrals supported on a parabolic times the opposite compact trace -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Haar Langlands.HarishChandraSchwartz
open Langlands.BruhatTits.DynamicUnipotentContainment

namespace Langlands.Plancherel.RationalDynamicSource

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] sourceGlobalPointTopology sourceGlobalPointMeasurable
  sourceGlobalPointBorel sourceGlobalFieldT2 sourceGlobalPointTopologicalGroup
  sourceGlobalPointT2 sourceGlobalPointLocallyCompact sourceGlobalPointNonarchimedean
  sourceGlobalFieldSecondCountable sourceGlobalPointSecondCountable subgroupSecondCountableGlobal

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))

set_option hygiene false in
local notation "Γ" => RationalPoint F G.X
set_option hygiene false in
local notation "P" => SubgroupFunctor.carrier (Dynamic.parabolic χ) (Over.mk (𝟙 (Spec (CommRingCat.of F))))
set_option hygiene false in
local notation "O" => unipotentPoints (oppositeCocharacter χ)

/-- For a connected reductive `G`, a left `P ∩ K`-invariant function supported on
`P (O ∩ K)` has its compact integral computed from the opposite compact trace at the
original inverse gamma scale. -/
def CompactOppositeCellIntegralStatement : Prop :=
  IsConnectedReductive G →
  ∀ f : Γ → ℂ, StronglyMeasurable f →
    (∀ p : P, (p : Γ) ∈ K → ∀ g : Γ, f ((p : Γ) * g) = f g) →
    (∀ g : Γ, f g ≠ 0 → ∃ p : P, ∃ v : O, (v : Γ) ∈ K ∧ g = (p : Γ) * (v : Γ)) →
    (∫ g in (K : Set Γ), f g ∂(ambientHaar K hK)) =
      ((gammaReal χ K hK : ℝ) : ℂ)⁻¹ *
        ∫ v in {v : O | (v : Γ) ∈ K}, f (v : Γ) ∂(radicalHaar (oppositeCocharacter χ) K hK)

set_option maxHeartbeats 1200000 in
/-- Restrict the published product Haar formula to the two literal compact traces. -/
theorem compactOppositeCellIntegral :
    CompactOppositeCellIntegralStatement χ K hK := by
  intro hG f hf hinv hsupp
  let : Smooth G.X.hom := hG.smooth
  let : LocallyCompactSpace P := (isClosed_dynamic_parabolic F G χ).locallyCompactSpace
  let : LocallyCompactSpace O := (isClosed_unipotentPoints (oppositeCocharacter χ)).locallyCompactSpace
  let μP := parabolicHaar χ K hK
  let μO := radicalHaar (oppositeCocharacter χ) K hK
  let KP : Set P := {p | (p : Γ) ∈ K}
  let KO : Set O := {v | (v : Γ) ∈ K}
  have hKP : MeasurableSet KP := K.isOpen.measurableSet.preimage measurable_subtype_coe
  have hKO : MeasurableSet KO := K.isOpen.measurableSet.preimage measurable_subtype_coe
  have hmass : μP KP = 1 := subgroupCompactOpenHaar_mass K hK P _
  have hcell := isOpenEmbedding_openCellMap_rationalPoint F G χ
  let F₀ := (K : Set Γ).indicator f
  let FP := KP.indicator (fun _ => (1 : ℂ))
  let FO := KO.indicator (fun v : O => f (v : Γ))
  have hpull : (fun x : P × O => F₀ (openCellMap x)) = fun x => FP x.1 * FO x.2⁻¹ := by
    funext x
    obtain ⟨p, v⟩ := x
    change (K : Set Γ).indicator f ((p : Γ) * (v : Γ)⁻¹) = FP p * FO v⁻¹
    by_cases hv : (v : Γ) ∈ K
    · have hvi : (v⁻¹ : O) ∈ KO := K.inv_mem hv
      rw [show FO v⁻¹ = f ((v : Γ)⁻¹) from Set.indicator_of_mem hvi _]
      by_cases hp : (p : Γ) ∈ K
      · have hpv : (p : Γ) * (v : Γ)⁻¹ ∈ (K : Set Γ) := K.mul_mem hp (K.inv_mem hv)
        rw [Set.indicator_of_mem hpv, hinv p hp,
          show FP p = 1 from Set.indicator_of_mem (show p ∈ KP from hp) _, one_mul]
      · have hnot : (p : Γ) * (v : Γ)⁻¹ ∉ (K : Set Γ) := by
          intro h
          have h' : (p : Γ) * (v : Γ)⁻¹ ∈ K := h
          have hmul := K.mul_mem h' hv
          rw [inv_mul_cancel_right] at hmul
          exact hp hmul
        rw [Set.indicator_of_notMem hnot,
          show FP p = 0 from Set.indicator_of_notMem (show p ∉ KP from hp) _, zero_mul]
    · have hvi : (v⁻¹ : O) ∉ KO := by
        intro h
        have hin := K.inv_mem (show ((v⁻¹ : O) : Γ) ∈ K from h)
        rw [Subgroup.coe_inv, inv_inv] at hin
        exact hv hin
      have hz : f ((p : Γ) * (v : Γ)⁻¹) = 0 := by
        by_contra h
        obtain ⟨p', v', hv', he⟩ := hsupp _ h
        have he' : openCellMap (p, v) = openCellMap (p', v'⁻¹) := by
          simpa only [openCellMap, Subgroup.coe_inv, inv_inv] using he
        have hvv := congrArg Prod.snd (hcell.injective he')
        change v = v'⁻¹ at hvv
        exact hvi (by rw [hvv, inv_inv]; exact hv')
      rw [show FO v⁻¹ = 0 from Set.indicator_of_notMem hvi _, mul_zero]
      by_cases h : (p : Γ) * (v : Γ)⁻¹ ∈ (K : Set Γ)
      · rw [Set.indicator_of_mem h, hz]
      · rw [Set.indicator_of_notMem h]
  have hFP : (∫ p, FP p ∂μP) = 1 := by
    rw [show FP = KP.indicator (fun _ => (1 : ℂ)) by rfl,
      integral_indicator hKP, setIntegral_const, measureReal_def, hmass, ENNReal.toReal_one, one_smul]
  have hFO : (∫ v : O, FO v⁻¹ ∂μO) = ∫ v in KO, f (v : Γ) ∂μO := by
    rw [integral_inv_eq_self FO μO, show FO = KO.indicator _ from rfl, integral_indicator hKO]
  rw [← integral_indicator K.isOpen.measurableSet, ambientHaar_eq_gamma_inv_smul χ K hK hG,
    integral_smul_measure, openCellMeasure, openCellProductPushforward,
    integral_map_of_stronglyMeasurable hcell.continuous.measurable (hf.indicator K.isOpen.measurableSet)]
  change ((gamma χ K hK)⁻¹).toReal • (∫ x : P × O, F₀ (openCellMap x) ∂(μP.prod μO)) = _
  rw [hpull, integral_prod_mul FP (fun v : O => FO v⁻¹), hFP, one_mul, hFO,
    ENNReal.toReal_inv, Complex.real_smul]
  congr 1
  simp only [gammaReal, Complex.ofReal_inv]

end Langlands.Plancherel.RationalDynamicSource
