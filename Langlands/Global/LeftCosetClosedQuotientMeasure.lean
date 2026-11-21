import Langlands.Analysis.Local.QuotientWeilKernel
import Langlands.Global.LeftCosetSubgroupSlice

/-! # Measure on the closed quotient of a discrete quotient -/

noncomputable section

universe u

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace

open Langlands.QuotientIntegration

variable {G : Type u} [Group G] {Γ H : Subgroup G}

/-- Passing from a left `Γ`-coset to the containing left `H`-coset. -/
def projectionOfLE (hle : Γ ≤ H) :
    Langlands.Global.LeftCosetSpace Γ → Langlands.Global.LeftCosetSpace H :=
  Quotient.map' id (fun _ _ h => QuotientGroup.rightRel_apply.mpr
    (hle (QuotientGroup.rightRel_apply.mp h)))

@[simp] theorem projectionOfLE_mk (hle : Γ ≤ H) (g : G) :
    projectionOfLE hle (mk Γ g) = mk H g :=
  rfl

variable [MeasurableSpace G]

theorem measurable_projectionOfLE (hle : Γ ≤ H) : Measurable (projectionOfLE hle) :=
  measurable_from_quotient.mpr (measurable_mk H)

variable [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [BorelSpace H] [BorelSpace (Langlands.Global.LeftCosetSpace H)]

/-- A unit-covolume discrete quotient in the closed subgroup gives the
compatible quotient measure under the natural projection. -/
def ClosedQuotientProjectionMeasureStatement
    (hle : Γ ≤ H) (hΓ : IsDiscrete (Γ : Set G))
    (μG : Measure G) [IsFiniteMeasureOnCompacts μG]
    (μH : Measure H) [SFinite μH] [IsFiniteMeasureOnCompacts μH]
    [μH.IsMulLeftInvariant] [μH.IsMulRightInvariant]
    (ν : Measure (Langlands.Global.LeftCosetSpace H)) : Prop :=
  IsClosed (H : Set G) → IsCompatible H μG μH ν →
    ∀ t : Set H, IsFundamentalDomain (Γ.comap H.subtype) t μH → μH t = 1 →
      MeasurePreserving (projectionOfLE hle) (discreteQuotientMeasure Γ hΓ μG) ν

/-- If the discrete quotient of the closed subgroup has mass one, the actual
projection from the discrete quotient of the ambient group transports its
fundamental-domain measure to the compatible closed-quotient measure. -/
theorem measurePreserving_projectionOfLE (hle : Γ ≤ H) (hΓ : IsDiscrete (Γ : Set G))
    (μG : Measure G) [IsFiniteMeasureOnCompacts μG]
    (μH : Measure H) [SFinite μH] [IsFiniteMeasureOnCompacts μH]
    [μH.IsMulLeftInvariant] [μH.IsMulRightInvariant]
    (ν : Measure (Langlands.Global.LeftCosetSpace H)) :
    ClosedQuotientProjectionMeasureStatement hle hΓ μG μH ν := by
  intro hH hν t ht hmass
  let d := fundamentalDomain Γ hΓ
  have hd : MeasurableSet d := measurableSet_fundamentalDomain Γ hΓ
  let : SecondCountableTopology H := secondCountableTopology_induced _ G Subtype.val
  let : Countable (Γ.comap H.subtype) := countable_of_isDiscrete _
    (hΓ.preimage continuous_subtype_val.continuousOn Subtype.val_injective)
  refine ⟨measurable_projectionOfLE hle, ?_⟩
  ext A hA
  let f : G → ℝ≥0∞ := (mk H ⁻¹' A).indicator 1
  have hPre : MeasurableSet (mk H ⁻¹' A) := measurable_mk H hA
  have hf : Measurable f := measurable_const.indicator hPre
  have hInv (h : H) (g : G) : f (h.val * g) = f g := by
    change A.indicator (fun _ => (1 : ℝ≥0∞)) (mk H (h.val * g)) =
      A.indicator (fun _ => (1 : ℝ≥0∞)) (mk H g)
    rw [mk_subgroup_mul]
  have hOrbit (q : Langlands.Global.LeftCosetSpace H) :
      ∫⁻ x, d.indicator f x ∂orbitKernel H hH μH q = A.indicator 1 q := by
    induction q using Quotient.inductionOn with
    | h g =>
      rw [orbitKernel_mk, lintegral_map (hf.indicator hd)
        (continuous_subtype_val.mul_const g).measurable]
      rw [lintegral_subgroupSlice_indicator Γ H hle hd
        (fundamentalDomain_unique Γ hΓ) μH ht f hInv g, hmass, one_mul]
      rfl
  calc
    _ = μG ((mk H ⁻¹' A) ∩ d) := by
      rw [Measure.map_apply (measurable_projectionOfLE hle) hA, discreteQuotientMeasure,
        quotientMeasure_apply Γ μG _ (measurable_projectionOfLE hle hA)]
      rfl
    _ = ∫⁻ x, d.indicator f x ∂μG := by
      rw [lintegral_indicator hd]
      change _ = ∫⁻ x, (mk H ⁻¹' A).indicator 1 x ∂μG.restrict d
      rw [lintegral_indicator_one hPre, Measure.restrict_apply hPre]
    _ = ∫⁻ q, ∫⁻ x, d.indicator f x ∂orbitKernel H hH μH q ∂ν :=
      (lintegral_orbitKernel H hH μH μG ν hν _ (hf.indicator hd)).symm
    _ = ν A := by
      simp_rw [hOrbit]
      exact lintegral_indicator_one hA

end Langlands.Global.LeftCosetSpace
