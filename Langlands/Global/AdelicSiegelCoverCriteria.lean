import Langlands.Global.AdelicSiegelNormOne
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Mathlib.Data.Set.Finite.Lattice

/-! # Forward coverage and uniform weak thresholds for actual Siegel products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise

namespace Langlands.Global

open Langlands.GroupScheme

namespace PositiveRealTorus

/-- A positive lower bound for finitely many indexed positive thresholds,
also defined for an empty index set. -/
def uniformCharacterThreshold {Index : Type*} (Δ : Set Index) (b : Index → ℝ≥0ˣ)
    (hΔ : Δ.Finite) : ℝ≥0ˣ :=
  (hΔ.image b).bddBelow.choose

/-- The chosen uniform threshold is at most each of the indexed thresholds. -/
theorem uniformCharacterThreshold_le {Index : Type*} (Δ : Set Index) (b : Index → ℝ≥0ˣ)
    (hΔ : Δ.Finite) (χ : Index) (hχ : χ ∈ Δ) :
    uniformCharacterThreshold Δ b hΔ ≤ b χ :=
  (hΔ.image b).bddBelow.choose_spec ⟨χ, hχ, rfl⟩

variable (F : Type u) [Field F] [NumberField F]
  (T₀ T : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)
  (Δ : Set (characterLattice T)) (b : characterLattice T → ℝ≥0ˣ)

/-- Finitely many positive indexed bounds admit a common positive lower bound,
including when the character set is empty. -/
theorem exists_uniform_weakCharacterChamber (hΔ : Δ.Finite) :
    ∃ t : ℝ≥0ˣ,
      weakCharacterChamber F T₀ T j Δ b ⊆
        weakCharacterChamber F T₀ T j Δ (fun _ => t) := by
  exact ⟨uniformCharacterThreshold Δ b hΔ,
    fun _ ha χ hχ => (uniformCharacterThreshold_le Δ b hΔ χ hχ).trans (ha χ hχ)⟩

/-- Indexed strict normalized inequalities imply one uniform weak normalized
inequality on any finite character set. -/
theorem exists_uniform_weakCharacterChamber_of_strict (hΔ : Δ.Finite) :
    ∃ t : ℝ≥0ˣ,
      strictCharacterChamber F T₀ T j Δ b ⊆
        weakCharacterChamber F T₀ T j Δ (fun _ => t) := by
  obtain ⟨t, ht⟩ := exists_uniform_weakCharacterChamber F T₀ T j Δ b hΔ
  exact ⟨t, (strictCharacterChamber_subset_weak F T₀ T j Δ b).trans ht⟩

end PositiveRealTorus

namespace AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- Rational left saturation covers the norm-one group precisely when every
norm-one point has a rational left translate in the specified set. -/
theorem normOne_subset_rational_mul_iff (S : Set (AdelicGroupPoints F G)) :
    (normOneSubgroup F G : Set (AdelicGroupPoints F G)) ⊆
        (rationalSubgroup F G : Set (AdelicGroupPoints F G)) * S ↔
      ∀ g : normOneSubgroup F G, ∃ q : RationalGroupPoints F G,
        rational F G q * (g : AdelicGroupPoints F G) ∈ S := by
  constructor
  · intro h g
    obtain ⟨_, ⟨q, rfl⟩, s, hs, hqs⟩ := h g.property
    refine ⟨q⁻¹, ?_⟩
    rw [map_inv, ← hqs, inv_mul_cancel_left]
    exact hs
  · intro h g hg
    obtain ⟨q, hq⟩ := h ⟨g, hg⟩
    refine ⟨rational F G q⁻¹, ⟨q⁻¹, rfl⟩, rational F G q * g, hq, ?_⟩
    change rational F G q⁻¹ * (rational F G q * g) = g
    rw [map_inv, inv_mul_cancel_left]

end AdelicGroupPoints

namespace AdelicSiegelFactors

open AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)
  (C : CompactFactors F G
    (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))

/-- The setup proves the containment direction of the Siegel-cover equality;
only its forward coverage and the original Iwasawa condition remain. -/
theorem IsSiegelAlgebraicSetup.isSiegelCover_iff_forward
    (h : IsSiegelAlgebraicSetup F G T i ν T₀ j) (t : ℝ≥0ˣ) :
    IsSiegelCover F G T i ν T₀ j C t ↔
      IsParabolicIwasawaCompact F G
          (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅)
          C.compactSubgroup ∧
        (normOneSubgroup F G : Set (AdelicGroupPoints F G)) ⊆
          (rationalSubgroup F G : Set (AdelicGroupPoints F G)) *
            weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν)
              C T₀ j t := by
  constructor
  · rintro ⟨hK, heq⟩
    exact ⟨hK, by rw [heq]⟩
  · rintro ⟨hK, hcover⟩
    exact ⟨hK, Set.Subset.antisymm
      (h.rational_mul_weakSiegelProduct_subset_normOne F G T i ν T₀ j C t) hcover⟩

/-- The actual cover predicate can equivalently use rational left translates
of individual norm-one points, with the canonical ordered product unchanged. -/
theorem IsSiegelAlgebraicSetup.isSiegelCover_iff_translate
    (h : IsSiegelAlgebraicSetup F G T i ν T₀ j) (t : ℝ≥0ˣ) :
    IsSiegelCover F G T i ν T₀ j C t ↔
      IsParabolicIwasawaCompact F G
          (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅)
          C.compactSubgroup ∧
        ∀ g : normOneSubgroup F G, ∃ q : RationalGroupPoints F G,
          rational F G q * (g : AdelicGroupPoints F G) ∈
            weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν)
              C T₀ j t := by
  rw [h.isSiegelCover_iff_forward F G T i ν T₀ j C t]
  exact and_congr_right fun _ => normOne_subset_rational_mul_iff F G _

variable [LocallyOfFiniteType G.X.hom]

/-- For an actual setup, coverage by a strict chamber with indexed positive
thresholds gives the exact weak-chamber Siegel cover with one positive threshold.
The original compact subgroup and both compact factor sets are preserved. -/
theorem IsSiegelAlgebraicSetup.exists_isSiegelCover_of_strictCover
    (h : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (hK : IsParabolicIwasawaCompact F G
      (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅)
      C.compactSubgroup)
    (b : characterLattice T → ℝ≥0ˣ)
    (hcover : (normOneSubgroup F G : Set (AdelicGroupPoints F G)) ⊆
      (rationalSubgroup F G : Set (AdelicGroupPoints F G)) *
        strictSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν)
          C T₀ j b) :
    ∃ t : ℝ≥0ˣ, IsSiegelCover F G T i ν T₀ j C t := by
  have hfinite := h.1.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  obtain ⟨t, ht⟩ :=
    PositiveRealTorus.exists_uniform_weakCharacterChamber_of_strict
      F T₀ T j (simpleRelativeRoots i ν) b hfinite
  refine ⟨t, (h.isSiegelCover_iff_forward F G T i ν T₀ j C t).mpr
    ⟨hK, hcover.trans ?_⟩⟩
  exact Set.mul_subset_mul_left
    (productSet_mono F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j ht)

end AdelicSiegelFactors

end Langlands.Global
