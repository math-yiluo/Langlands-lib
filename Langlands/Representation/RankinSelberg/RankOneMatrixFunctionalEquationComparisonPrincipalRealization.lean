import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalWeighted
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxCoefficient
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierAveraging

/-! # Actual bi-smooth realization on the uniform principal box -/

noncomputable section

namespace Langlands.RankinSelberg.RankOneBox

open MeasureTheory Topology GeneralLinear HarmonicAnalysis Whittaker Conductor RankOneIwasawa
open UnequalRankMirabolicUnitTest
open scoped NNReal ENNReal

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance principalRealizationTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance principalRealizationValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance principalRealizationLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance principalRealizationT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance principalRealizationGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance principalRealizationGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

local notation "𝓛" => F.canonicalTopologicalData.additiveLattice
local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable (ψ : UnitaryAdditiveCharacter F.Carrier) {m : ℕ} {V : Type uV}
  [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)

/-- The determinant reduction on a model box only needs q ≤ A. -/
theorem modelFunction_eq_determinantRankOne_of_mem_box_of_le {A q : ℤ} {a : ℕ}
    (ha : 0 < a) (hqA : q ≤ A)
    (hL : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ j, j ≠ 0 →
      y.val 0 j ∈ 𝓛 (q - A))
    (hψ : ∀ z ∈ 𝓛 q, ψ z = 1)
    (hlev : ∀ z ∈ levelSet F.Carrier a, z ∈ 𝓛 q)
    (hstab : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * y) = glModelFunction ψ (m + 1) σ ℓ w g)
    (hDstab : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * determinantRankOne (m + 1) y) =
        glModelFunction ψ (m + 1) σ ℓ w g)
    {g : Langlands.GeneralLinear (m + 1 + 1) F.Carrier}
    (hg : g.val ∈ box F A q a) :
    glModelFunction ψ (m + 1) σ ℓ w g =
      glModelFunction ψ (m + 1) σ ℓ w (determinantRankOne (m + 1) g) := by
  obtain ⟨y, hy, hb⟩ := exists_mem_principalLevel_mul_inv_upper F ha hg
  obtain ⟨⟨⟨g₁, t⟩, u⟩, hx⟩ := exists_point_eq (g * y⁻¹) hb
  have hbox : (point ((g₁, t), u)).val ∈ box F A q a := by
    rw [hx, Units.val_mul]
    exact (mul_mem_box_iff_of_le F hqA hL g.val (inv_mem hy)).2 hg
  have ht := torusFactor_mem F ha (mem_torusBox_of_mem_box F hbox)
  have hu : u ∈ unipotentBox F q a := by
    have h := hbox
    rw [point_eq_mul F, Units.val_mul,
      mul_mem_box_iff_of_le F hqA hL _ ht, mem_box_unipotent_mul_iff] at h
    exact h.2
  have hW : glModelFunction ψ (m + 1) σ ℓ w (point ((g₁, t), u)) =
      glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g₁) := by
    rw [point_eq_mul F, hstab _ ht, glModelFunction_equivariance,
      standardCharacter_eq_one F ψ hψ hlev hu, one_mul]
    rfl
  calc
    glModelFunction ψ (m + 1) σ ℓ w g =
        glModelFunction ψ (m + 1) σ ℓ w (g * y⁻¹) := (hstab _ (inv_mem hy) g).symm
    _ = glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g₁) := by rw [← hx]; exact hW
    _ = glModelFunction ψ (m + 1) σ ℓ w
        (determinantRankOne (m + 1) (g * y⁻¹)) := by
      rw [← hx, determinantRankOne_point F]
      rfl
    _ = glModelFunction ψ (m + 1) σ ℓ w (determinantRankOne (m + 1) g) := by
      rw [map_mul, hDstab _ (inv_mem hy)]

/-- One actual normalized left-average coefficient realizes the original model
vector on the precise uniform extraction box and retains its right principal
invariance. The compact averaging subgroup fixes the full matrix test. -/
def PrincipalModelRealization (hσ : IsSmooth σ) (a : ℕ)
    (K : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F.Carrier))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier))) : Prop :=
  let c := F.canonicalTopologicalData.additiveConductor ψ
  let f := GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ ℓ K hK w
  0 < a ∧ 0 ≤ c + a ∧
    (∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * y) = glModelFunction ψ (m + 1) σ ℓ w g) ∧
    (∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * determinantRankOne (m + 1) y) =
        glModelFunction ψ (m + 1) σ ℓ w g) ∧
    (∀ k ∈ K,
      (∀ M, boxLatticeTest F (c + a) c a (k.val * M) = boxLatticeTest F (c + a) c a M) ∧
        abv (Matrix.det k.val) = 1) ∧
    (∀ g : Langlands.GeneralLinear (m + 1 + 1) F.Carrier,
      g.val ∈ box F (c + a) c a → f.val g = glModelFunction ψ (m + 1) σ ℓ w g) ∧
    (∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g, f.val (g * y) = f.val g)

/-- Every original smooth model vector has such a realization at arbitrary
additive conductor, with independent field and representation universes. -/
theorem exists_principalModelRealization (hσ : IsSmooth σ) :
    ∃ (a : ℕ) (K : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F.Carrier))
      (hK : IsCompact (K : Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier))),
      PrincipalModelRealization F ψ σ ℓ w hσ a K hK := by
  let c := F.canonicalTopologicalData.additiveConductor ψ
  obtain ⟨Kw, hKw⟩ := glModel_isSmooth ψ (m + 1) σ hσ ℓ w
  let KD := Kw.comap (determinantRankOne (m + 1)) (continuous_determinantRankOne (m + 1))
  obtain ⟨a₀, ha₀, ha₀U⟩ := exists_pos_principalLevelOpenSubgroup_subset F.Carrier (m + 1)
    ((Kw ⊓ KD).isOpen.mem_nhds (one_mem _))
  let a : ℕ := a₀ + (-c).toNat + 1
  have ha : 0 < a := by dsimp [a]; omega
  have hA : 0 ≤ c + a := by
    have h := Int.self_le_toNat (-c)
    dsimp [a]
    omega
  have hsuba : principalLevelSubgroup F.Carrier (m + 1) a ≤
      principalLevelSubgroup F.Carrier (m + 1) a₀ :=
    principalLevelSubgroup_antitone F.Carrier (m + 1) (by dsimp [a]; omega)
  have hmemU : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a,
      y ∈ Kw ⊓ KD := fun y hy => ha₀U (hsuba hy)
  have hstab : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * y) = glModelFunction ψ (m + 1) σ ℓ w g := by
    intro y hy g
    have hfix : glModelRepresentation ψ (m + 1) σ ℓ y w = w := hKw ⟨y, (hmemU y hy).1⟩
    rw [← glModelFunction_translate, hfix]
  have hDstab : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * determinantRankOne (m + 1) y) =
        glModelFunction ψ (m + 1) σ ℓ w g := by
    intro y hy g
    have hfix : glModelRepresentation ψ (m + 1) σ ℓ (determinantRankOne (m + 1) y) w = w :=
      hKw ⟨determinantRankOne (m + 1) y, (hmemU y hy).2⟩
    rw [← glModelFunction_translate, hfix]
  have hL : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ j, j ≠ 0 →
      y.val 0 j ∈ 𝓛 (c - (c + a)) := fun _ hy => principalLevel_firstRow F c a hy
  have hψ : ∀ z ∈ 𝓛 c, ψ z = 1 :=
    (F.canonicalTopologicalData.additiveTrivialAt_iff_le_conductor ψ c).2 le_rfl
  have hlev : ∀ z ∈ levelSet F.Carrier a, z ∈ 𝓛 c := by
    intro z hz
    rw [levelSet_eq_additiveLattice F] at hz
    exact lattice_mono F (by omega) hz
  let Φ := boxLatticeTest F (n := m + 1) (c + a) c a
  obtain ⟨K₀, hK₀, hΦ⟩ := GodementJacquet.Padic.exists_compactOpen_matrixTest_invariant F Φ
  obtain ⟨K, hK, hsub⟩ := F.canonicalTopologicalData.generalLinearCompactOpen (m + 1 + 1)
    (((K₀ ⊓ KD : OpenSubgroup _) : Set _)) ((K₀ ⊓ KD).isOpen.mem_nhds (one_mem _))
  refine ⟨a, K, hK, ha, hA, hstab, hDstab, (fun k hk => hΦ k (hsub hk).1), ?_, ?_⟩
  · intro g hg
    apply averagedModelCoefficient_eq_of_left_invariant F ψ σ ℓ w hσ K hK g
    intro k hk
    have hkg : (k * g).val ∈ box F (c + a) c a := by
      have h := (hΦ k (hsub hk).1).1 g.val
      dsimp only [Φ] at h
      simp only [boxLatticeTest_apply] at h
      rw [Set.indicator_of_mem hg] at h
      by_contra hn
      change k.val * g.val ∉ box F (c + a) c a at hn
      rw [Set.indicator_of_notMem hn] at h
      exact zero_ne_one h
    rw [modelFunction_eq_determinantRankOne_of_mem_box_of_le F ψ σ ℓ w ha (by omega) hL hψ hlev
        hstab hDstab hkg,
      modelFunction_eq_determinantRankOne_of_mem_box_of_le F ψ σ ℓ w ha (by omega) hL hψ hlev
        hstab hDstab hg, map_mul]
    have hcomm : determinantRankOne (m + 1) k * determinantRankOne (m + 1) g =
        determinantRankOne (m + 1) g * determinantRankOne (m + 1) k := by
      unfold determinantRankOne
      change Iwasawa.diagonalUnits _ * Iwasawa.diagonalUnits _ =
        Iwasawa.diagonalUnits _ * Iwasawa.diagonalUnits _
      rw [← map_mul, ← map_mul, mul_comm]
    rw [hcomm, ← glModelFunction_translate]
    have hfix : glModelRepresentation ψ (m + 1) σ ℓ (determinantRankOne (m + 1) k) w = w :=
      hKw ⟨determinantRankOne (m + 1) k, (hsub hk).2⟩
    rw [hfix]
  · intro y hy g
    simp only [GodementJacquet.Padic.averagedModelCoefficient_apply,
      GodementJacquet.normalizedLeftAverage]
    congr 1
    apply setIntegral_congr_fun K.isOpen.measurableSet
    intro k hk
    change glModelFunction ψ (m + 1) σ ℓ w (k * (g * y)) =
      glModelFunction ψ (m + 1) σ ℓ w (k * g)
    rw [← mul_assoc, hstab y hy]

end Langlands.RankinSelberg.RankOneBox
