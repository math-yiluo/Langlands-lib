import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonMatrixSynthesis
import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonBox
import Langlands.Group.GL.CountabilityProof
import Mathlib.MeasureTheory.Integral.Prod

/-! Compact support and genuine product integrability for the unipotent Fourier exchange. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg.CompactWhittakerSynthesis

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis GeneralLinear Topology

universe uK uF

section General

variable {K : Type uK} [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T2Space K]

/-- A compact matrix set with determinant in the compact determinant image of a
compact group set lifts to a compact set in the actual general linear group. -/
theorem isCompact_matrixDetRestriction (r : ℕ)
    (S : Set (Langlands.GeneralLinear r K)) (hS : IsCompact S)
    (T : Set (Matrix (Fin r) (Fin r) K)) (hT : IsCompact T) :
    IsCompact {g : Langlands.GeneralLinear r K | g.val ∈ T ∧
      g.val.det ∈ (fun a : Langlands.GeneralLinear r K => a.val.det) '' S} := by
  let D := (fun a : Langlands.GeneralLinear r K => a.val.det) '' S
  have hD : IsCompact D := hS.image Units.continuous_val.matrix_det
  have hE : IsCompact (T ∩ Matrix.det ⁻¹' D) :=
    hT.inter_right (hD.isClosed.preimage continuous_id.matrix_det)
  have hrange : T ∩ Matrix.det ⁻¹' D ⊆
      Set.range (Units.val : Langlands.GeneralLinear r K → Matrix (Fin r) (Fin r) K) := by
    rintro A ⟨_, a, ha, hdet⟩
    have hn : A.det ≠ 0 := hdet ▸ a.det_ne_zero
    exact ⟨((Matrix.isUnit_iff_isUnit_det A).mpr (Ne.isUnit hn)).unit, rfl⟩
  exact (isEmbedding_generalLinear_val r).isInducing.isCompact_preimage' hE hrange

/-- A group test at `u*g` and an ambient matrix test at `g` have joint compact
support when the closed subgroup has determinant one. -/
theorem hasCompactSupport_group_matrix_product (r : ℕ)
    (H : Subgroup (Langlands.GeneralLinear r K))
    (hH : IsClosed (H : Set (Langlands.GeneralLinear r K)))
    (hdet : ∀ u : H, u.val.val.det = 1)
    (φ : SchwartzBruhat (Langlands.GeneralLinear r K))
    (Φ : SchwartzBruhat (Matrix (Fin r) (Fin r) K)) :
    HasCompactSupport (fun z : H × Langlands.GeneralLinear r K =>
      φ (z.1.val * z.2) * Φ z.2.val) := by
  let S := tsupport (φ : Langlands.GeneralLinear r K → ℂ)
  let D := {g : Langlands.GeneralLinear r K | g.val ∈ tsupport (Φ : _ → ℂ) ∧
    g.val.det ∈ (fun a : Langlands.GeneralLinear r K => a.val.det) '' S}
  have hD : IsCompact D := isCompact_matrixDetRestriction r S φ.hasCompactSupport
    (tsupport (Φ : _ → ℂ)) Φ.hasCompactSupport
  let A := (fun z : Langlands.GeneralLinear r K × Langlands.GeneralLinear r K =>
    z.1 * z.2⁻¹) '' (S ×ˢ D)
  have hA : IsCompact A := (φ.hasCompactSupport.prod hD).image
    (continuous_fst.mul continuous_snd.inv)
  have hU : IsCompact ((Subtype.val : H → Langlands.GeneralLinear r K) ⁻¹' A) :=
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage hA
  apply HasCompactSupport.intro (hU.prod hD)
  intro z hz
  by_contra hne
  have hφ : z.1.val * z.2 ∈ S :=
    subset_tsupport (φ : _ → ℂ) ((mul_ne_zero_iff.mp hne).1)
  have hΦ : z.2.val ∈ tsupport (Φ : _ → ℂ) :=
    subset_tsupport (Φ : _ → ℂ) ((mul_ne_zero_iff.mp hne).2)
  have hg : z.2 ∈ D := by
    refine ⟨hΦ, z.1.val * z.2, hφ, ?_⟩
    change (z.1.val * z.2).val.det = z.2.val.det
    rw [Units.val_mul, Matrix.det_mul, hdet z.1, one_mul]
  apply hz
  refine ⟨?_, hg⟩
  change z.1.val ∈ A
  exact ⟨(z.1.val * z.2, z.2), ⟨hφ, hg⟩, by simp⟩

/-- Multiplying by arbitrary continuous subgroup and group weights preserves
actual integrability for any supplied measures finite on compact sets. -/
theorem integrable_weighted_group_matrix_product (r : ℕ)
    (H : Subgroup (Langlands.GeneralLinear r K))
    (hH : IsClosed (H : Set (Langlands.GeneralLinear r K)))
    (hdet : ∀ u : H, u.val.val.det = 1)
    [SecondCountableTopology (Langlands.GeneralLinear r K)]
    [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (Langlands.GeneralLinear r K)]
    [BorelSpace (Langlands.GeneralLinear r K)]
    (μH : Measure H) (μG : Measure (Langlands.GeneralLinear r K))
    [SFinite μG] [IsFiniteMeasureOnCompacts μH] [IsFiniteMeasureOnCompacts μG]
    (φ : SchwartzBruhat (Langlands.GeneralLinear r K))
    (Φ : SchwartzBruhat (Matrix (Fin r) (Fin r) K))
    (a : H → ℂ) (b : Langlands.GeneralLinear r K → ℂ)
    (ha : Continuous a) (hb : Continuous b) :
    Integrable (fun z : H × Langlands.GeneralLinear r K =>
      a z.1 * φ (z.1.val * z.2) * Φ z.2.val * b z.2) (μH.prod μG) := by
  have hc : HasCompactSupport (fun z : H × Langlands.GeneralLinear r K =>
      a z.1 * (φ (z.1.val * z.2) * Φ z.2.val) * b z.2) :=
    (hasCompactSupport_group_matrix_product r H hH hdet φ Φ).mul_left.mul_right
  have hcont : Continuous (fun z : H × Langlands.GeneralLinear r K =>
      a z.1 * (φ (z.1.val * z.2) * Φ z.2.val) * b z.2) :=
    ((ha.comp continuous_fst).mul
      ((φ.continuous.comp ((continuous_subtype_val.comp continuous_fst).mul continuous_snd)).mul
        (Φ.continuous.comp (Units.continuous_val.comp continuous_snd)))).mul
      (hb.comp continuous_snd)
  simpa only [mul_assoc] using hcont.integrable_of_hasCompactSupport hc

/-- Restriction to the group retains compact support if the ambient topological
support lies entirely in the invertible locus. -/
def matrixTestOnGroup (r : ℕ)
    (Φ : SchwartzBruhat (Matrix (Fin r) (Fin r) K))
    (hΦ : tsupport (Φ : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear r K → Matrix (Fin r) (Fin r) K)) :
    SchwartzBruhat (Langlands.GeneralLinear r K) :=
  ⟨fun g => Φ g.val,
    Φ.locallyConstant.comp_continuous Units.continuous_val,
    HasCompactSupport.intro
      ((isEmbedding_generalLinear_val r).isInducing.isCompact_preimage'
        Φ.hasCompactSupport hΦ)
      (fun g hg => by
        by_contra hne
        exact hg (subset_tsupport (Φ : _ → ℂ) hne))⟩

omit [T2Space K] in
@[simp] theorem matrixTestOnGroup_apply (r : ℕ)
    (Φ : SchwartzBruhat (Matrix (Fin r) (Fin r) K))
    (hΦ : tsupport (Φ : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear r K → Matrix (Fin r) (Fin r) K))
    (g : Langlands.GeneralLinear r K) :
    matrixTestOnGroup r Φ hΦ g = Φ g.val := rfl

end General

section CanonicalPadic

open Whittaker

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.upperUnipotentLocallyCompactSpace (n + 1)
local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- The actual inverse-character and determinant weighted product is integrable
against the unchanged unipotent and general-linear Haar measures. -/
theorem integrable_unipotent_group_matrix_product
    (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (φ : SchwartzBruhat (Langlands.GeneralLinear (n + 1) F.Carrier))
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) (s : ℂ) :
    Integrable (fun z : upperUnipotent (n + 1) F.Carrier ×
        Langlands.GeneralLinear (n + 1) F.Carrier =>
      (((standardCharacter ψ n z.1)⁻¹ : ℂˣ) : ℂ) * φ (z.1.val * z.2) *
        Φ z.2.val * determinantWeight abv z.2 s)
      ((unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) := by
  exact integrable_weighted_group_matrix_product (n + 1)
    (upperUnipotent (n + 1) F.Carrier) UpperUnipotent.isClosed
    (fun u => unipotent_det u)
    (unipotentHaar F.Carrier n) (generalLinearHaar F.Carrier n) φ Φ
    (fun u => (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ))
    (fun g => determinantWeight abv g s)
    (Units.continuous_val.comp (continuous_inv.comp
      (standardCharacterContinuous ψ n).continuous))
    (RankOneBox.continuous_determinantWeight F (n + 1) s)

/-- The same bound for a full-matrix first test whose ambient support consists
of invertible matrices, as supplied by extension of a group test. -/
theorem integrable_unipotent_matrix_product
    (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (Φ₁ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (hΦ₁ : tsupport (Φ₁ : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear (n + 1) F.Carrier →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) (s : ℂ) :
    Integrable (fun z : upperUnipotent (n + 1) F.Carrier ×
        Langlands.GeneralLinear (n + 1) F.Carrier =>
      (((standardCharacter ψ n z.1)⁻¹ : ℂˣ) : ℂ) * Φ₁ (z.1.val * z.2).val *
        Φ z.2.val * determinantWeight abv z.2 s)
      ((unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) :=
  integrable_unipotent_group_matrix_product F ψ n (matrixTestOnGroup (n + 1) Φ₁ hΦ₁) Φ s

/-- Genuine product integrability justifies exchanging the actual Haar integrals. -/
theorem integral_unipotent_matrix_swap
    (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (Φ₁ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (hΦ₁ : tsupport (Φ₁ : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear (n + 1) F.Carrier →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) (s : ℂ) :
    (∫ u : upperUnipotent (n + 1) F.Carrier,
      ∫ g : Langlands.GeneralLinear (n + 1) F.Carrier,
        (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) * Φ₁ (u.val * g).val *
          Φ g.val * determinantWeight abv g s
        ∂generalLinearHaar F.Carrier n ∂unipotentHaar F.Carrier n) =
    ∫ g : Langlands.GeneralLinear (n + 1) F.Carrier,
      ∫ u : upperUnipotent (n + 1) F.Carrier,
        (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) * Φ₁ (u.val * g).val *
          Φ g.val * determinantWeight abv g s
        ∂unipotentHaar F.Carrier n ∂generalLinearHaar F.Carrier n :=
  integral_integral_swap (integrable_unipotent_matrix_product F ψ n Φ₁ hΦ₁ Φ s)

end CanonicalPadic

end Langlands.RankinSelberg.CompactWhittakerSynthesis
