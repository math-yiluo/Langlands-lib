import Langlands.BaseChange.RegularOrbitalProfilesFromCharts
import Langlands.JacquetLanglands.DivisionUnitCompactQuotient
import Langlands.JacquetLanglands.RegularDivisionCentralizer
import Langlands.JacquetLanglands.RegularDivisionOrbitalProfileStatement

/-! # The normalized orbital profiles of regular division units -/

noncomputable section

namespace Langlands.JacquetLanglands

open Set MeasureTheory _root_.Topology
open Langlands.BaseChange Langlands.CentralSimple Langlands.QuotientIntegration Langlands.TraceFormula
open Langlands.Topology (HasCompactOpenNeighborhoodBasis hasCompactOpenNeighborhoodBasis_of_mathlib)

universe u

section Chart

variable {F D : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D] [TopologicalSpace D] [IsModuleTopology F D]
  [IsTopologicalRing D]

local notation "d" => reducedDegree F D
local notation "R" => {a : Dˣ // IsRegular F D a}
local notation "θ" => MonoidHom.id Dˣ

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
  [TopologicalSpace D] [IsModuleTopology F D] [IsTopologicalRing D] in
private theorem isRegular_twistedConj_id {a : Dˣ} (ha : IsRegular F D a) (g : Dˣ) :
    IsRegular F D (twistedConj θ g a) := by
  change (reducedCharpoly F D (g⁻¹ * a * g : Dˣ).val).Separable
  rw [reducedCharpoly_unit_conj]
  exact ha

/-- Conjugation gives a product chart over a small compact open coefficient window. -/
private theorem exists_regularDivisionOrbitalChart
    (hB : HasCompactOpenNeighborhoodBasis (Fin d → F)) (a : R) :
    ∃ c : RegularOrbitalChart θ (fun r : R => divisionCoefficients F D r.val),
      divisionCoefficients F D a.val ∈ c.parameters := by
  let : T2Space Dˣ := units_t2Space F D
  let p (r : R) := divisionCoefficients F D r.val
  obtain ⟨U, s₀, hU, haU, hs₀, hp₀, hH₀⟩ := exists_regularDivisionCoefficientSection F D a.property
  obtain ⟨V, haV, hV, hVc, hVU⟩ := hB (p a) U (hU.mem_nhds haU)
  let i (b : V) : U := ⟨b.val, hVU b.property⟩
  let s (b : V) : Dˣ := s₀ (i b)
  have hs : Continuous s := hs₀.comp (continuous_subtype_val.subtype_mk _)
  let H := divisionCentralizer (a : Dˣ)
  have hH (b : V) : divisionCentralizer (s b) = H := (hH₀ (i b)).2
  have hcenter : Subgroup.center Dˣ ≤ H := by
    change Subgroup.center Dˣ ≤ divisionCentralizer (a : Dˣ)
    rw [divisionCentralizer_eq_centralizer]
    exact Subgroup.center_le_centralizer _
  let : CompactSpace (LeftQuotient H) := compactSpace_leftQuotient_divisionUnits F D H hcenter
  let : CompactSpace V := isCompact_iff_compactSpace.mp hVc
  let orbit (b : V) : LeftQuotient H → Dˣ := descend H (fun g => twistedConj θ g (s b))
    (fun c g => by
      have hc : (c : Dˣ) ∈ divisionCentralizer (s b) := by
        rw [hH b]
        exact c.property
      exact twistedConj_left_mul θ (s b) ⟨c.val, hc⟩ g)
  have hp (b : V) (q : LeftQuotient H) : divisionCoefficients F D (orbit b q) = b.val := by
    induction q using Quotient.inductionOn with
    | h g => exact (divisionCoefficients_conj F D g (s b)).trans (hp₀ (i b))
  have hreg (b : V) (q : LeftQuotient H) : IsRegular F D (orbit b q) := by
    induction q using Quotient.inductionOn with
    | h g => exact isRegular_twistedConj_id (hH₀ (i b)).1 g
  let fn (z : V × LeftQuotient H) : (p ⁻¹' V : Set R) :=
    ⟨⟨orbit z.1 z.2, hreg z.1 z.2⟩, by
      change divisionCoefficients F D (orbit z.1 z.2) ∈ V
      rw [hp]
      exact z.1.property⟩
  let param (x : (p ⁻¹' V : Set R)) : V := ⟨p x.val, x.property⟩
  have hparam (z : V × LeftQuotient H) : param (fn z) = z.1 := Subtype.ext (hp z.1 z.2)
  have hcont : Continuous fn := by
    let q : V × Dˣ → V × LeftQuotient H := Prod.map id (leftQuotientMap H)
    have hq : IsOpenQuotientMap q := IsOpenQuotientMap.id.prodMap (leftQuotient_isOpenQuotientMap H)
    apply hq.continuous_comp_iff.mp
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_snd.inv.mul (hs.comp continuous_fst)).mul continuous_snd
  have hinj : Function.Injective fn := by
    rintro ⟨b, q⟩ ⟨b', q'⟩ heq
    have hb : b = b' := (hparam _).symm.trans ((congrArg param heq).trans (hparam _))
    subst b'
    revert heq
    induction q using Quotient.inductionOn with
    | h g =>
      induction q' using Quotient.inductionOn with
      | h g' =>
        intro heq
        have hgg := congrArg (fun x : (p ⁻¹' V : Set R) => x.val.val) heq
        change twistedConj θ g (s b) = twistedConj θ g' (s b) at hgg
        congr 1
        apply Quotient.sound
        change QuotientGroup.rightRel H g g'
        rw [QuotientGroup.rightRel_apply, ← hH b, mem_twistedCentralizer]
        rw [← twistedConj_apply, ← twistedConj_mul, ← hgg, twistedConj_mul, mul_inv_cancel,
          twistedConj_one]
  have hsurj : Function.Surjective fn := by
    intro x
    have hx : divisionCoefficients F D (s (param x)) = divisionCoefficients F D x.val.val :=
      hp₀ (i (param x))
    obtain ⟨g, hg⟩ := exists_divisionConj_of_regular_coefficients_eq F D (hH₀ (i (param x))).1 hx
    exact ⟨(param x, leftQuotientMap H g), Subtype.ext (Subtype.ext hg)⟩
  let e := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective fn ⟨hinj, hsurj⟩) hcont
  exact ⟨{
    parameters := V
    isOpen := hV
    centralizer := H
    representative := fun b => ⟨s b, (hH₀ (i b)).1⟩
    chart := e
    stabilizer := hH
    parameter := fun z => hp z.1 z.2
    apply_mk := fun _ _ => rfl }, haV⟩

end Chart

/-- The division side of regular transfer has a compactly supported orbital profile. -/
theorem regularDivisionOrbitalProfile : RegularDivisionOrbitalProfileStatement.{u} := by
  intro F _ _ _ _ _ D _ _ _ _ _ _
  let : IsTopologicalRing D := isTopologicalRing F D
  intro _ _ μ _
  let : T2Space F := LocalFieldTopology.t2Space F
  let : SecondCountableTopology F := LocalFieldTopology.secondCountableTopology F
  let : TotallyDisconnectedSpace F := LocalFieldTopology.totallyDisconnectedSpace F
  let : T2Space Dˣ := units_t2Space F D
  let : LocallyCompactSpace Dˣ := units_locallyCompactSpace F D
  let : SecondCountableTopology D :=
    (coordinateHomeomorph F D (Module.finBasis F D)).secondCountableTopology
  let : SecondCountableTopology Dˣ :=
    (finiteAlgebra_isOpenEmbedding_unitsVal (F := F) (A := D)).isEmbedding.secondCountableTopology
  let : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  let : μ.IsMulRightInvariant := divisionUnits_haar_rightInvariant F D μ
  let R : Set Dˣ := {a | IsRegular F D a}
  let p (a : R) := divisionCoefficients F D a.val
  have hB : HasCompactOpenNeighborhoodBasis (Fin (reducedDegree F D) → F) :=
    hasCompactOpenNeighborhoodBasis_of_mathlib
  have horbit (a : R) (g : Dˣ) :
      ∃ s : R, (s : Dˣ) = twistedConj (MonoidHom.id Dˣ) g a ∧ p s = p a :=
    ⟨⟨twistedConj (MonoidHom.id Dˣ) g a, isRegular_twistedConj_id a.property g⟩, rfl,
      divisionCoefficients_conj F D g a⟩
  obtain ⟨m, hm⟩ := RegularOrbitalMeasures.exists_isNormalized
    (θ := MonoidHom.id Dˣ) (μ := μ) (R := R) continuous_id
    (fun a => divisionCentralizer_hasLargestCompactOpenSubgroup F D a.property)
    (fun a => divisionCentralizer_mul_comm F D a.property)
  exact ⟨m, hm, regularOrbitalProfilesFromCharts (MonoidHom.id Dˣ) continuous_id μ R
    (isOpen_regularDivision F D) p ((continuous_divisionCoefficients F D).comp continuous_subtype_val)
    hB horbit (exists_regularDivisionOrbitalChart hB) m hm⟩

end Langlands.JacquetLanglands
