import Langlands.Global.AdelicSplitTorusCharacterBox
import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # Compact rational representatives for ambient norm-one root boxes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme PositiveRealTorus Langlands.LinearAlgebra.RationalSpan

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Torus points with ambient norm one and two-sided bounds on simple-root norms. -/
def ambientNormOneRootBox (b : ℝ≥0) : Set (AdelicGroupPoints F T.toGrp) :=
  {x | map F T.toGrp G i x ∈ normOneSubgroup F G ∧
    x ∈ torusCharacterBox F T (simpleRelativeRoots i ν) b}

omit [IsAffineHom G.X.hom] in
/-- Ambient norm one kills the norms of every restricted ambient rational character. -/
theorem normCharacter_restrict_eq_one_of_map_mem_normOne
    {x : AdelicGroupPoints F T.toGrp}
    (hx : map F T.toGrp G i x ∈ normOneSubgroup F G)
    (χ : rationalCharacters G) :
    normCharacter F T (torusCharacterRestrict i χ) x = 1 := by
  change characterNorm F T.toGrp (i ≫ χ.toMul) x = 1
  rw [characterNorm_comp]
  exact (mem_normOneSubgroup F G _).mp hx χ.toMul

omit [NumberField F] in
/-- Simple roots and restricted ambient characters span the full rational character
space of an actual maximal split torus. -/
theorem simpleRelativeRoots_restrictedCharacters_ratSpan_eq_top
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) :
    ratSpan (simpleRelativeRoots i ν ∪ Set.range (torusCharacterRestrict i)) = ⊤ := by
  let := hi.isSplitSubtorus.mono
  have hroots := relativeRootSystem F G hG T i hi
  have hsimple := ratSpan_simpleRelativeRoots_eq_relativeRootSpan i ν hν
    (fun _ hα => hroots.neg_mem_relativeRoots i hi.1.1 hα)
  change Submodule.span ℚ
    (toRat '' (simpleRelativeRoots i ν ∪ Set.range (torusCharacterRestrict i))) = ⊤
  rw [Set.image_union, Submodule.span_union, ← rationalCharacterRestrictRat_range]
  change ratSpan (simpleRelativeRoots i ν) ⊔
    (rationalCharacterRestrictRat i).range = ⊤
  rw [hsimple]
  exact hG.relativeRootSpan_sup_restrictionRange_eq_top i hi

/-- On the ambient norm-one locus, a simple-root box also bounds all restricted
ambient characters. This supplies the central directions missing from root bounds. -/
theorem ambientNormOneRootBox_subset_characterBox (b : ℝ≥0) (hb : 1 ≤ b) :
    ambientNormOneRootBox F G T i ν b ⊆
      torusCharacterBox F T
        (simpleRelativeRoots i ν ∪ Set.range (torusCharacterRestrict i)) b := by
  intro x hx χ hχ
  rcases hχ with hχ | ⟨ψ, rfl⟩
  · exact hx.2 χ hχ
  · rw [normCharacter_restrict_eq_one_of_map_mem_normOne F G T i hx.1 ψ]
    change b⁻¹ ≤ 1 ∧ 1 ≤ b
    exact ⟨inv_le_one₀ (zero_lt_one.trans_le hb) |>.mpr hb, hb⟩

/-- Uniform simple-root bounds and ambient norm one construct compact principal
representatives in the entire maximal split torus, including its central directions. -/
theorem exists_isCompact_rational_mul_mem_ambientNormOneRootBox
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (b : ℝ≥0) (hb : 1 ≤ b) :
    ∃ K : Set (AdelicGroupPoints F T.toGrp), IsCompact K ∧
      ∀ x ∈ ambientNormOneRootBox F G T i ν b,
        ∃ q : RationalGroupPoints F T.toGrp, rational F T.toGrp q * x ∈ K := by
  obtain ⟨K, hK, hcover⟩ := exists_isCompact_rational_mul_mem_characterBox F T hi.1.1
    (simpleRelativeRoots_restrictedCharacters_ratSpan_eq_top F G T i ν hG hi hν) b
  exact ⟨K, hK, fun x hx =>
    hcover x (ambientNormOneRootBox_subset_characterBox F G T i ν b hb hx)⟩

end Langlands.Global.AdelicGroupPoints
