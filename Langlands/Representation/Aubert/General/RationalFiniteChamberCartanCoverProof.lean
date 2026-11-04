import Langlands.Representation.Aubert.General.RationalFiniteChamberCartanCoverStatement
import Langlands.Representation.Aubert.General.RationalEndpoint
import Langlands.Group.FiniteChamberCartanCoverProof
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups

/-! # Actual full-center uniformizer charts from the supplied Cartan witness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.Cartan
open Langlands.BruhatTits.SpecialCompact Langlands.Plancherel.RenardCartan
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General.RationalPointFamily

/-- The actual Cartan witness yields natural-coordinate charts modulo the full center. -/
theorem rationalFiniteChamberCartanCover : RationalFiniteChamberCartanCoverStatement.{u} := by
  intro F _ _ _ _ G hG S i hi ν
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  intro _ hν hStandard D x Z j s h hsj hK hcompat F₀ hF₀
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  classical
  have hfull : levi i ν Finset.univ = ⊤ := levi_univ_eq_top i ν hStandard hG hi hν
  have hexists (I : Finset (SimpleRoot i ν)) :
      ∃ ζ, IsStandardCocharacter i ν (rootSet i ν I) ζ :=
    (hStandard F G hG S i hi ν hν _ (rootSet_subset i ν I)).1
  have hstd (I : Finset (SimpleRoot i ν)) : ∃ ζ : cocharacterLattice S,
      (∀ β ∈ I, simpleRootPairing i ν β ζ = 0) ∧
        ∀ β ∉ I, 0 < simpleRootPairing i ν β ζ := by
    obtain ⟨ζ, hζ⟩ := hexists I
    exact ⟨ζ, fun β hβ => hζ.2.1 β.1 ((val_mem_rootSet i ν I β).mpr hβ),
      fun β hβ => hζ.2.2 β.1 β.2 fun h' => hβ ((val_mem_rootSet i ν I β).mp h')⟩
  have hfinite : (simpleRelativeRoots i ν).Finite := Set.finite_coe_iff.mp inferInstance
  have hcentral (c : cocharacterLattice S) (hc : ∀ α, simpleRootPairing i ν α c = 0) :
      uniformizerPowers i (.ofAdd c) ∈ Subgroup.center (rationalPoints G) := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    exact commute_uniformizerPowers i ν hfinite Finset.univ (hexists _) c
      (fun β _ => hc β) g (by rw [hfull]; exact Subgroup.mem_top _)
  obtain ⟨jM, _, _, _, _, _, _, hlat⟩ := hcompat ∅ (Set.empty_subset _)
  obtain ⟨B, hB⟩ := exists_rep_rationalCartanSet i ν j s h hsj hlat.1 hF₀.1 Finset.univ
  apply finiteChamberCartanCover (SimpleRoot i ν) (cocharacterLattice S) (rationalPoints G)
    (D.specialCompactSubgroup x : Set (rationalPoints G)) hK.2.1.1
    (uniformizerPowers i) (simpleRootPairing i ν) (rationalPoints.map j '' F₀)
    (hF₀.1.image _) hstd hcentral B
  intro g
  obtain ⟨k₁, hk₁, t, ht, k₂, hk₂, hg⟩ := exists_cartan_levi D x ν hcompat hF₀
    Finset.univ g (by rw [hfull]; exact Subgroup.mem_top _)
  obtain ⟨c, f, hf, htcf, hc⟩ := hB t ht
  refine ⟨k₁, hk₁.1, c, f, hf, k₂, hk₂.1, fun α => hc α (Finset.mem_univ α), ?_⟩
  simpa only [htcf, mul_assoc] using hg

end Langlands.Aubert.General.RationalPointFamily
