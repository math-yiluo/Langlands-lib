import Langlands.Sheaf.Renard.CompactSectionStalksStatement

/-!
# Proof: stalks are quotients of compact sections

Renard (9 July 2026), II.2.5, Remarque, printed p.42 / PDF p.48:
`F_x = F_c(X) / ⟨f · φ, f(x) = 0⟩`.
Surjectivity of the canonical map is the published `stalkQuotientMap_surjective`.
Injectivity: a compact section with zero germ at `x` has compact support avoiding `x`;
a compact open containing that support and avoiding `x` has a characteristic function
vanishing at `x` and fixing the section, so the section lies in the span.
-/

noncomputable section

namespace Langlands.Sheaf.Renard.CompactSectionStalks

open Langlands.HarmonicAnalysis
open Langlands.Sheaf.Renard.VectorSheafScalars Langlands.Sheaf.Renard.CompactSectionTestModule

/-- With a compact open neighbourhood basis, a compact subset of an open set lies in a
compact open contained in that open set. -/
theorem exists_isCompact_isOpen_between {X : Type} [TopologicalSpace X]
    (hX : Langlands.Topology.HasCompactOpenNeighborhoodBasis X) {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V : Set X, IsOpen V ∧ IsCompact V ∧ K ⊆ V ∧ V ⊆ U := by
  choose W hyW hWo hWc hWU using fun y (hy : y ∈ K) => hX y U (hU.mem_nhds (hKU hy))
  obtain ⟨t, hKt⟩ := hK.elim_nhds_subcover' W fun y hy => (hWo y hy).mem_nhds (hyW y hy)
  exact ⟨⋃ y ∈ t, W y.1 y.2, isOpen_biUnion fun y _ => hWo _ _,
    t.isCompact_biUnion fun y _ => hWc _ _, hKt, Set.iUnion₂_subset fun y _ => hWU _ _⟩

variable {X : Type} [TopologicalSpace X] (F : VectorSheaf X) (x : X)

/-- A compact section whose germ at `x` vanishes lies in `⟨f · φ, f(x) = 0⟩`. -/
theorem mem_vanishingSpan_of_germ_eq_zero (hX : Langlands.Topology.IsLocallyProfinite X)
    (s : CompactSupport.submodule F.presheaf) (hs : CompactGerms.germ F x s = 0) :
    s ∈ vanishingSpan F x := by
  have : T2Space X := hX.t2Space
  have hxs : x ∉ CompactSupport.support F.presheaf s.1 := fun h => h hs
  obtain ⟨V, hVo, hVc, hsV, hVx⟩ :=
    exists_isCompact_isOpen_between hX.2
      (show IsCompact (CompactSupport.support F.presheaf s.1) from s.2)
      isOpen_compl_singleton (Set.subset_compl_singleton_iff.2 hxs)
  have hV : IsClopen V := ⟨hVc.isClosed, hVo⟩
  have hfx : PointwiseTestAlgebra.characteristic hV hVc x = 0 := by
    rw [PointwiseTestAlgebra.characteristic_apply,
      Set.indicator_of_notMem (fun h => hVx h rfl)]
  rw [← characteristic_smul_eq_self F hV hVc s hsV]
  exact smul_mem_vanishingSpan F x hfx s

/-- Injectivity of the canonical map `F_c(X) / ⟨f · φ, f(x) = 0⟩ → F_x`. -/
theorem stalkQuotientMap_injective (hX : Langlands.Topology.IsLocallyProfinite X) :
    Function.Injective (stalkQuotientMap F x) := by
  rw [← LinearMap.ker_eq_bot]
  refine Submodule.ker_liftQ_eq_bot _ _ _ ?_
  intro s hs
  exact mem_vanishingSpan_of_germ_eq_zero F x hX s (LinearMap.mem_ker.1 hs)

/-- Renard II.2.5 Remarque: the canonical map `F_c(X) / ⟨f · φ, f(x) = 0⟩ → F_x`
is bijective on every t.d. space, for every complex vector sheaf and every point. -/
theorem stalkQuotientComparison : StalkQuotientComparison := by
  intro X _ hX F x
  exact ⟨stalkQuotientMap_injective F x hX, stalkQuotientMap_surjective F x hX⟩

end Langlands.Sheaf.Renard.CompactSectionStalks
