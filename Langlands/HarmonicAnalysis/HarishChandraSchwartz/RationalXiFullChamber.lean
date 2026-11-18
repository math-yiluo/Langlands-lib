import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalChamberSection
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiUpperBoundStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSquareIntegrableDecay
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.XiCompactComparison
import Langlands.Geometry.Building.CentralizerDatumOfStructure
import Langlands.GroupScheme.Rational.MinimalStandardDynamicComparison
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # Transporting the lattice Xi upper bound to the full chamber

Compact torus-kernel thickening preserves the Xi polynomial estimate.
The substantive lattice Xi upper theorem remains an explicit input to
the final implication.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

section CompactExtension

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {P K : Subgroup Γ} {hPK : IsIwasawaPair P K} {δ : P →* ℝ≥0ˣ}
  {Ξ σ : Γ → ℝ} {C T : Set Γ}

/-- Compact left thickening inside the parabolic preserves a polynomial
Xi estimate with its exact Iwasawa half-weight. -/
theorem xiUpperBound_iwasawa_compact_mul
    (hδ : ∀ p : P, (p : Γ) ∈ K → δ p = 1)
    (hKo : IsOpen (K : Set Γ))
    (hΞ : ∀ g, 0 ≤ Ξ g) (htrans : UniformTranslationBound Ξ)
    (hKΞ : ∀ k ∈ K, ∀ g, Ξ (k * g) = Ξ g)
    (hσ : ∀ g, 0 ≤ σ g) (hσc : Continuous σ)
    (hsub : ∀ g h, σ (g * h) ≤ σ g + σ h) (hinv : ∀ g, σ g⁻¹ = σ g)
    (hC : IsCompact C) (hCP : C ⊆ (P : Set Γ))
    (hup : XiUpperBound Ξ σ T (iwasawaWeight hPK δ)) :
    XiUpperBound Ξ σ (C * T) (iwasawaWeight hPK δ) := by
  obtain ⟨c, d, hupper⟩ := hup
  obtain ⟨L, hL⟩ := htrans.exists_uniform_left hΞ hKo hKΞ hC
  obtain ⟨D, hD⟩ := hC.bddAbove_image hσc.continuousOn
  have hwc := continuous_iwasawaWeight (hPK := hPK) hδ hKo
  have hwp (g : Γ) : 0 < iwasawaWeight hPK δ g := iwasawaWeight_pos g
  obtain ⟨B, hB⟩ := hC.bddAbove_image (hwc.inv₀ (fun g => (hwp g).ne')).continuousOn
  let A : ℝ := 1 + max D 0
  have hA : 1 ≤ A := by dsimp [A]; linarith [le_max_right D 0]
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  refine ⟨max L 0 * max c 0 * max B 0 * A ^ |d|, d, ?_⟩
  rintro a ⟨k, hk, b, hb, rfl⟩
  have hkD : σ k ≤ D := hD ⟨k, hk, rfl⟩
  have hcomp : 1 + σ (k * b) ≤ A * (1 + σ b) := by
    have hs := hsub k b
    have hn := hσ b
    have hD0 := le_max_left D 0
    dsimp [A]
    nlinarith [le_max_right D 0]
  have hcomp' : 1 + σ b ≤ A * (1 + σ (k * b)) := by
    have hs := hsub k⁻¹ (k * b)
    rw [inv_mul_cancel_left, hinv] at hs
    have hn := hσ (k * b)
    have hD0 := le_max_left D 0
    dsimp [A]
    nlinarith [le_max_right D 0]
  have hpow := rpow_le_rpow_abs_mul_of_le
    (by linarith [hσ (k * b)]) (by linarith [hσ b]) hA hcomp hcomp' d
  have hwk : iwasawaWeight hPK δ k = NNReal.sqrt (δ ⟨k, hCP hk⟩ : ℝ≥0) := by
    simpa only [mul_one] using
      iwasawaWeight_mul (hPK := hPK) hδ (hCP hk) K.one_mem
  have hwkb : iwasawaWeight hPK δ (k * b) =
      iwasawaWeight hPK δ k * iwasawaWeight hPK δ b := by
    rw [hwk]
    exact iwasawaWeight_mul_left (hPK := hPK) hδ ⟨k, hCP hk⟩ b
  have hwb : iwasawaWeight hPK δ b ≤ max B 0 * iwasawaWeight hPK δ (k * b) := by
    have hkinv : (iwasawaWeight hPK δ k)⁻¹ ≤ max B 0 :=
      (hB ⟨k, hk, rfl⟩).trans (le_max_left B 0)
    calc
      iwasawaWeight hPK δ b =
          (iwasawaWeight hPK δ k)⁻¹ * iwasawaWeight hPK δ (k * b) := by
        rw [hwkb, ← mul_assoc, inv_mul_cancel₀ (hwp k).ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hkinv (hwp _).le
  have hL0 : 0 ≤ max L 0 := le_max_right _ _
  have hc0 : 0 ≤ max c 0 := le_max_right _ _
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hupper' : Ξ b ≤ max c 0 * iwasawaWeight hPK δ b * (1 + σ b) ^ d :=
    (hupper b hb).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left c 0) (hwp b).le)
      (Real.rpow_nonneg (by linarith [hσ b]) _))
  calc
    Ξ (k * b) ≤ max L 0 * Ξ b :=
      (hL k hk b).trans (mul_le_mul_of_nonneg_right (le_max_left L 0) (hΞ b))
    _ ≤ max L 0 * (max c 0 * iwasawaWeight hPK δ b * (1 + σ b) ^ d) :=
      mul_le_mul_of_nonneg_left hupper' hL0
    _ ≤ max L 0 * (max c 0 * (max B 0 * iwasawaWeight hPK δ (k * b)) *
        (A ^ |d| * (1 + σ (k * b)) ^ d)) := by
      gcongr
      · exact Real.rpow_nonneg (by linarith [hσ b]) _
      · exact mul_nonneg hc0 (mul_nonneg hB0 (hwp _).le)
    _ = _ := by ring

end CompactExtension

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The full maximal split torus itself is a compatible split component
of the minimal Levi. -/
theorem isCompatibleStandardSplitComponent_minimal_id
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) :
    IsCompatibleStandardSplitComponent i ν ∅ S (𝟙 S.toGrp) := by
  obtain ⟨Z, j, hj, hjc⟩ :=
    fieldCentralizerRepresentability F S G hi.1.1.isAffineHom i
  let a := torusCentralizerFactor i hj
  refine ⟨⟨hi.isSplitSubtorus.1, IsClosedSubgroup.of_iso (Iso.refl _)⟩,
    Z, j, a, ?_, hjc, ?_, hi.isSplitComponent_torusCentralizerFactor hj hjc, ?_⟩
  · rwa [standardLevi_empty_eq_torusCentralizer_of_generic i ν hG hi hν]
  · exact hi.1.1.isConnectedReductive_centralizer_of_dynamic dynamicCentralizerReductive hG i j hj hjc
  · simpa only [Category.id_comp] using torusCentralizerFactor_comp i hj

/-- The exact full-chamber Xi upper estimate follows from the substantive
lattice-section Xi upper theorem, with all compact and section transports
proved here. -/
theorem RationalXiUpperBoundStatement.fullChamberXiUpperBound
    (h : RationalXiUpperBoundStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    {K0 : Subgroup (rationalPoints G)} (hbasis : SimultaneousStandardBasisAt i ν K0)
    {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    {N : ℕ} [Nonempty (Fin N)] {ρ : MatrixRepresentation G (Fin N)}
    (hρ : IsClosedSubgroup ρ) :
    XiUpperBound (rationalXi hKc hPK) (rationalHeight (F := F) ρ)
      (rationalMinimalChamber i ν) (iwasawaWeight hPK (rationalMinimalModulus i ν)) := by
  have hsection := h.xiUpperBound hG hi hν hbasis
    (isCompatibleStandardSplitComponent_minimal_id hG hi hν) hKo hKc hPK hρ
  rw [rationalMinimalChamber_eq_compactKernel_mul_section i ν hi.isSplitSubtorus.1]
  exact xiUpperBound_iwasawa_compact_mul
    (fun p hp => rationalMinimalModulus_eq_one i ν hKo hKc p hp) hKo
    (rationalXi_nonneg hKc hPK) (rationalXi_uniformTranslationBound hKo hKc hPK)
    (fun k hk g => by simpa only [mul_one] using rationalXi_mul_mul hKo hKc hPK hk K.one_mem g)
    (rationalHeight_nonneg ρ) (continuous_rationalHeight ρ)
    (rationalHeight_mul_le ρ) (rationalHeight_inv ρ)
    (isCompact_rationalMinimalTorusCompactKernel i hi.isSplitSubtorus.1)
    (fun k hk => by
      obtain ⟨x, hx, rfl⟩ := hk
      apply rationalMinimalChamber_subset_minimalParabolic i ν
      refine ⟨x, ?_, rfl⟩
      ·
          rw [Langlands.BruhatTits.Cartan.RenardLeviCones.mem_componentPlus_iff_order,
            Langlands.BruhatTits.Cartan.RenardLeviCones.restrictedSimpleCharacters_minimal]
          intro α hα
          rw [characterOrder_eq_zero_of_mem_normKernel hx α])
    hsection

end Rational

/-- The actual Xi upper estimate on the whole minimal-torus chamber,
with only the same simultaneous-basis structural input as the lattice
upper statement. -/
def RationalXiFullChamberUpperBoundStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ K0 : Subgroup (rationalPoints G), SimultaneousStandardBasisAt i ν K0 →
    ∀ K : Subgroup (rationalPoints G), IsOpen (K : Set (rationalPoints G)) →
    ∀ (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
      XiUpperBound (rationalXi hKc hPK) (rationalHeight (F := F) ρ)
        (rationalMinimalChamber i ν) (iwasawaWeight hPK (rationalMinimalModulus i ν))

/-- The lattice upper statement implies the full-chamber upper statement;
the substantive Xi upper proof is not supplied by this implication. -/
theorem rationalXiFullChamberUpperBound_of_upperBound
    (h : RationalXiUpperBoundStatement.{u}) : RationalXiFullChamberUpperBoundStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν K0 hbasis K hKo hKc hPK N _ ρ hρ
  exact h.fullChamberXiUpperBound hG hi hν hbasis hKo hKc hPK hρ

end Langlands.HarishChandraSchwartz
