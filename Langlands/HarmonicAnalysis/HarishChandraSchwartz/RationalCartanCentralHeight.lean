import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCartanCellHeight
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalValuationCoordinates

/-! # Cartan-cell height bounds with the central valuation retained -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LinearAlgebra.RationalSpan
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

universe u

/-- An integer linear functional on a finite coordinate lattice has a linear
norm bound, including the zero-dimensional case. -/
theorem exists_norm_pi_int_hom_le {J : Type*} [Fintype J] [DecidableEq J]
    (φ : (J → ℤ) →+ ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖φ x‖ ≤ C * ‖x‖ := by
  refine ⟨∑ j, ‖φ (Pi.single j 1)‖, Finset.sum_nonneg fun j _ => norm_nonneg _, fun x => ?_⟩
  have hsingle (j : J) : (fun i : J => if j = i then (1 : ℤ) else 0) = Pi.single j 1 := by
    funext i
    simp only [Pi.single_apply, eq_comm]
  have hx : φ x = ∑ j, x j * φ (Pi.single j 1) := by
    simpa only [smul_eq_mul, hsingle, AddMonoidHom.coe_toIntLinearMap] using
      φ.toIntLinearMap.pi_apply_eq_sum_univ x
  rw [hx]
  calc ‖∑ j, x j * φ (Pi.single j 1)‖ ≤ ∑ j, ‖x j * φ (Pi.single j 1)‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖x‖ * ‖φ (Pi.single j 1)‖ := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_le_pi_norm x j) (norm_nonneg _)
    _ = (∑ j, ‖φ (Pi.single j 1)‖) * ‖x‖ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

/-- Evaluation of one rational character's valuation in the existing image
lattice coordinates. -/
def rationalValuationCoordinateEvaluation (hG : IsConnectedReductive G) (χ : rationalCharacters G) :
    (Fin (rationalImageRank G) → ℤ) →+ ℤ :=
  let E : Additive (rationalDiscreteValuationImage G) →+ ℤ :=
    { toFun := fun x => x.toMul.val.toAdd χ
      map_zero' := rfl
      map_add' _ _ := rfl }
  E.comp (rationalValuationLatticeEquiv G hG).symm.toAddMonoidHom

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
@[simp]
theorem rationalValuationCoordinateEvaluation_apply (hG : IsConnectedReductive G)
    (χ : rationalCharacters G) (g : rationalPoints G) :
    rationalValuationCoordinateEvaluation hG χ (rationalValuationCoordinates G hG g) =
      (rationalCharacterValuation G g).toAdd χ := by
  change (((rationalValuationLatticeEquiv G hG).symm
    (rationalValuationLatticeEquiv G hG (Additive.ofMul (rationalValuationImageProjection G g)))).toMul.val).toAdd χ = _
  rw [AddEquiv.symm_apply_apply]
  rfl

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- Every rational-character valuation is bounded by a constant times the norm
of the existing central valuation coordinates. -/
theorem exists_abs_rationalCharacterValuation_le_coordinates (hG : IsConnectedReductive G)
    (χ : rationalCharacters G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : rationalPoints G,
      |((rationalCharacterValuation G g).toAdd χ : ℝ)| ≤ C * ‖rationalValuationCoordinates G hG g‖ := by
  obtain ⟨C, hC, hb⟩ := exists_norm_pi_int_hom_le (rationalValuationCoordinateEvaluation hG χ)
  refine ⟨C, hC, fun g => ?_⟩
  simpa only [rationalValuationCoordinateEvaluation_apply, Int.norm_eq_abs] using
    hb (rationalValuationCoordinates G hG g)

/-- On an arbitrary Cartan cell, full matrix height is bounded by the simple-root
pairings and the central valuation coordinates of the actual group point. -/
theorem exists_rationalHeight_le_cartanCell_coordinates (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (F0 : Finset (centralizerPoints i)) {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : cocharacterLattice S) (T : ℝ), 0 ≤ T →
      (∀ β : Langlands.Aubert.General.RationalPointFamily.SimpleRoot i ν,
        |(Langlands.Aubert.General.simpleRootPairing i ν β y : ℝ)| ≤ T) →
      ∀ g ∈ rationalCartanCell i K0 F0 y,
        rationalHeight (F := F) ρ g ≤ C * (1 + T + ‖rationalValuationCoordinates G hG g‖) := by
  classical
  have hK0 := compactSubgroup_le_rationalCommonNormKernel G K0 hK0c
  obtain ⟨b, hb⟩ := hK0c.bddAbove_image (continuous_rationalHeight (F := F) ρ).continuousOn
  obtain ⟨b', hb'⟩ := (F0.image fun f : centralizerPoints i =>
    rationalHeight (F := F) ρ (f : rationalPoints G)).exists_le
  let P : cocharacterLattice S → ℝ → Prop := fun y t =>
    1 ≤ t ∧ (∀ β : Langlands.Aubert.General.RationalPointFamily.SimpleRoot i ν,
      |(Langlands.Aubert.General.simpleRootPairing i ν β y : ℝ)| ≤ t) ∧
      ∃ g ∈ rationalCartanCell i K0 F0 y, ‖rationalValuationCoordinates G hG g‖ ≤ t
  have hroot : ∀ β : Langlands.Aubert.General.RationalPointFamily.SimpleRoot i ν, ∃ C : ℝ,
      ∀ y t, P y t → |(latticePairing S β.1 y : ℝ)| ≤ C * t :=
    fun β => ⟨1, fun y t hP => by simpa using hP.2.1 β⟩
  have hres : ∀ χ : rationalCharacters G, ∃ C : ℝ,
      ∀ y t, P y t → |(latticePairing S (torusCharacterRestrict i χ) y : ℝ)| ≤ C * t := by
    intro χ
    obtain ⟨A, hA, hAb⟩ := exists_abs_rationalCharacterValuation_le_coordinates hG χ
    obtain ⟨V, hV⟩ := (F0.image fun f : centralizerPoints i =>
      |((rationalCharacterValuation G (f : rationalPoints G)).toAdd χ : ℝ)|).exists_le
    refine ⟨A + |V|, fun y t hP => ?_⟩
    obtain ⟨ht, -, g, hg, hgt⟩ := hP
    obtain ⟨k₁, hk₁, k₂, hk₂, f, hf, rfl⟩ := hg
    have hkχ₁ := (mem_rationalCommonNormKernel_iff_valuation G _).mp (hK0 hk₁) χ
    have hkχ₂ := (mem_rationalCommonNormKernel_iff_valuation G _).mp (hK0 hk₂) χ
    have hpair : (rationalCharacterValuation G
        (Langlands.Aubert.General.uniformizerPowers i (.ofAdd y))).toAdd χ =
        latticePairing S (torusCharacterRestrict i χ) y := by
      simp only [Langlands.Aubert.General.uniformizerPowers, MonoidHom.comp_apply,
        RenardCartan.rationalCharacterValuation_map_uniformizerSection]
      rfl
    have hvalue : ((rationalCharacterValuation G
        (k₁ * Langlands.Aubert.General.uniformizerPowers i (.ofAdd y) * (f : rationalPoints G) * k₂)).toAdd χ : ℝ) =
        (latticePairing S (torusCharacterRestrict i χ) y : ℝ) +
          ((rationalCharacterValuation G (f : rationalPoints G)).toAdd χ : ℝ) := by
      simp only [map_mul, toAdd_mul, AddMonoidHom.add_apply, hkχ₁, hkχ₂, zero_add, add_zero,
        Int.cast_add, hpair]
    have hgA := (hAb (k₁ * Langlands.Aubert.General.uniformizerPowers i (.ofAdd y) *
      (f : rationalPoints G) * k₂)).trans (mul_le_mul_of_nonneg_left hgt hA)
    have hfV := (hV _ (Finset.mem_image_of_mem _ hf)).trans (le_abs_self V)
    have hdiff : |(latticePairing S (torusCharacterRestrict i χ) y : ℝ)| ≤
        |((rationalCharacterValuation G
          (k₁ * Langlands.Aubert.General.uniformizerPowers i (.ofAdd y) * (f : rationalPoints G) * k₂)).toAdd χ : ℝ)| +
          |((rationalCharacterValuation G (f : rationalPoints G)).toAdd χ : ℝ)| := by
      rw [hvalue]
      simpa only [add_neg_cancel_right, abs_neg] using abs_add_le ((latticePairing S (torusCharacterRestrict i χ) y : ℝ) +
        ((rationalCharacterValuation G (f : rationalPoints G)).toAdd χ : ℝ))
        (-((rationalCharacterValuation G (f : rationalPoints G)).toAdd χ : ℝ))
    have hVt : |V| ≤ |V| * t := le_mul_of_one_le_right (abs_nonneg _) ht
    calc |(latticePairing S (torusCharacterRestrict i χ) y : ℝ)|
        ≤ A * t + |V| := hdiff.trans (add_le_add hgA hfV)
      _ ≤ (A + |V|) * t := by nlinarith
  obtain ⟨Idx, _, α, M, hM, hσ⟩ :=
    exists_rationalHeight_uniformizerPowers_le_sum hi.isSplitSubtorus.1 i ρ
  choose Cα hCα using fun k => exists_abs_latticePairing_le_of_simpleRoots hG hi hν hroot hres (α k)
  let C : ℝ := |2 * b + b'| + ∑ k, M k * |Cα k|
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun k _ => mul_nonneg (hM k) (abs_nonneg _))
  refine ⟨C, hC, fun y T hT hβ g hg => ?_⟩
  let t : ℝ := 1 + T + ‖rationalValuationCoordinates G hG g‖
  have ht : 1 ≤ t := by dsimp [t]; linarith [norm_nonneg (rationalValuationCoordinates G hG g)]
  have hP : P y t := ⟨ht, fun β => (hβ β).trans (by dsimp [t]; linarith [norm_nonneg (rationalValuationCoordinates G hG g)]),
    g, hg, by dsimp [t]; linarith⟩
  have hsum : rationalHeight (F := F) ρ (Langlands.Aubert.General.uniformizerPowers i (.ofAdd y)) ≤
      ∑ k, M k * |Cα k| * t := by
    refine (hσ y).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ((hCα k y t hP).trans ?_) (hM k)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (le_trans (by norm_num) ht)
  obtain ⟨k₁, hk₁, k₂, hk₂, f, hf, rfl⟩ := hg
  have h₁ : rationalHeight (F := F) ρ k₁ ≤ b := hb ⟨k₁, hk₁, rfl⟩
  have h₂ : rationalHeight (F := F) ρ k₂ ≤ b := hb ⟨k₂, hk₂, rfl⟩
  have h₃ : rationalHeight (F := F) ρ (f : rationalPoints G) ≤ b' := hb' _ (Finset.mem_image_of_mem _ hf)
  have e₁ := rationalHeight_mul_le (F := F) ρ
    (k₁ * Langlands.Aubert.General.uniformizerPowers i (.ofAdd y) * (f : rationalPoints G)) k₂
  have e₂ := rationalHeight_mul_le (F := F) ρ
    (k₁ * Langlands.Aubert.General.uniformizerPowers i (.ofAdd y)) (f : rationalPoints G)
  have e₃ := rationalHeight_mul_le (F := F) ρ k₁ (Langlands.Aubert.General.uniformizerPowers i (.ofAdd y))
  have habs : 2 * b + b' ≤ |2 * b + b'| * t :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) ht)
  change _ ≤ C * t
  dsimp only [C]
  rw [add_mul, Finset.sum_mul]
  linarith

/-- With a fixed bound on all simple-root pairings, the full height grows at
most linearly in the central valuation coordinates, uniformly over all cells. -/
theorem exists_one_add_height_le_coordinates_on_bounded_cells (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (F0 : Finset (centralizerPoints i)) {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) (T : ℝ) (hT : 0 ≤ T) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ y : cocharacterLattice S,
      (∀ β : Langlands.Aubert.General.RationalPointFamily.SimpleRoot i ν,
        |(Langlands.Aubert.General.simpleRootPairing i ν β y : ℝ)| ≤ T) →
      ∀ g ∈ rationalCartanCell i K0 F0 y,
        1 + rationalHeight (F := F) ρ g ≤ D * (1 + ‖rationalValuationCoordinates G hG g‖) := by
  obtain ⟨C, hC, hb⟩ := exists_rationalHeight_le_cartanCell_coordinates hG hi hν hK0c F0 ρ
  refine ⟨1 + C * (1 + T), by nlinarith, fun y hβ g hg => ?_⟩
  have h := hb y T hT hβ g hg
  have hn := norm_nonneg (rationalValuationCoordinates G hG g)
  have hCT : 0 ≤ C * T * ‖rationalValuationCoordinates G hG g‖ :=
    mul_nonneg (mul_nonneg hC hT) hn
  nlinarith

end Langlands.HarishChandraSchwartz
