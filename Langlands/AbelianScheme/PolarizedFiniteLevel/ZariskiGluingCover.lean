import Mathlib.AlgebraicGeometry.RelativeGluing

/-! # The locally directed cover by opens contained in a member of an open cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluing

variable {S : Scheme.{u}} {ι : Type*} (U : ι → S.Opens)

/-- The opens of `S` contained in some member of the family `U`. -/
def SubOpens : Type u := {W : S.Opens // ∃ i, W ≤ U i}

instance : PartialOrder (SubOpens U) :=
  inferInstanceAs (PartialOrder {W : S.Opens // ∃ i, W ≤ U i})

variable {U}

/-- If `U` covers `S`, so do the opens contained in some member of `U`. -/
theorem isOpenCover_subOpens (hU : iSup U = ⊤) :
    TopologicalSpace.IsOpenCover (fun W : SubOpens U => W.1) := by
  apply top_unique
  intro x _
  have hx : x ∈ iSup U := by rw [hU]; trivial
  rw [TopologicalSpace.Opens.mem_iSup] at hx ⊢
  obtain ⟨i, hi⟩ := hx
  exact ⟨⟨U i, i, le_rfl⟩, hi⟩

/-- The open cover of `S` by all opens contained in some member of `U`. -/
def subCover (hU : iSup U = ⊤) : S.OpenCover :=
  S.openCoverOfIsOpenCover (fun W : SubOpens U => W.1) (isOpenCover_subOpens hU)

instance (hU : iSup U = ⊤) : PartialOrder (subCover hU).I₀ :=
  inferInstanceAs (PartialOrder (SubOpens U))

theorem subCover_le_iff (hU : iSup U = ⊤) {W W' : (subCover hU).I₀} :
    W ≤ W' ↔ ((subCover hU).f W).opensRange ≤ ((subCover hU).f W').opensRange := by
  change W.1 ≤ W'.1 ↔ W.1.ι.opensRange ≤ W'.1.ι.opensRange
  rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]

theorem subCover_isBasis (hU : iSup U = ⊤) :
    TopologicalSpace.Opens.IsBasis
      (Set.range fun W : (subCover hU).I₀ => ((subCover hU).f W).opensRange) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro V x hxV
  have hx : x ∈ iSup U := by rw [hU]; trivial
  rw [TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨i, hi⟩ := hx
  refine ⟨V ⊓ U i, ⟨⟨V ⊓ U i, i, inf_le_right⟩, ?_⟩, ⟨hxV, hi⟩, inf_le_left⟩
  exact Scheme.Opens.opensRange_ι _

instance (hU : iSup U = ⊤) : (subCover hU).LocallyDirected :=
  .ofIsBasisOpensRange (subCover_le_iff hU) (subCover_isBasis hU)

instance (hU : iSup U = ⊤) : Small.{u} (subCover hU).I₀ :=
  inferInstanceAs (Small.{u} (SubOpens U))

instance (hU : iSup U = ⊤) : Quiver.IsThin (subCover hU).I₀ :=
  inferInstanceAs (Quiver.IsThin (SubOpens U))

theorem subCover_trans (hU : iSup U = ⊤) {W W' : (subCover hU).I₀} (h : W ⟶ W') :
    (subCover hU).trans h = S.homOfLE (leOfHom h) := by
  have hm : Mono ((subCover hU).f W') := inferInstanceAs (Mono (W'.1.ι))
  apply (cancel_mono ((subCover hU).f W')).mp
  rw [Scheme.Cover.trans_map]
  exact (Scheme.homOfLE_ι S (leOfHom h)).symm

end Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluing
