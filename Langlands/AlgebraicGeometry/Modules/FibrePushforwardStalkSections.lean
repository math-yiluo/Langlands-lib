import Langlands.AlgebraicGeometry.Modules.FibreNeighbourhoodSections
import Mathlib.Topology.Sheaves.Stalks

/-! # The canonical map from a pushforward stalk to fibre sections -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (M : X.Modules)

/-- The compatible restrictions to the fibre form a cocone on base neighbourhoods. -/
def fibreSectionCocone :
    Cocone ((OpenNhds.inclusion s).op ⋙ ((Scheme.Modules.pushforward f).obj M).presheaf) where
  pt := ((Scheme.Modules.pullback (f.fiberι s)).obj M).presheaf.obj (op ⊤)
  ι :=
    { app := fun V =>
        ((Scheme.Modules.pullbackPushforwardAdjunction (f.fiberι s)).unit.app M).app
          (f ⁻¹ᵁ V.unop.1) ≫
        ((Scheme.Modules.pullback (f.fiberι s)).obj M).presheaf.map
          (homOfLE (fibre_preimage_neighbourhood f s V.unop.2)).op
      naturality := by
        intro V W i
        ext τ
        exact fibreNeighbourhoodSection_restrict f s M V.unop.2 W.unop.2
          i.unop.le τ }

/-- The actual restriction from the pushforward stalk at `s` to fibre sections. -/
def fibrePushforwardStalkSection :
    ((Scheme.Modules.pushforward f).obj M).presheaf.stalk s ⟶
      ((Scheme.Modules.pullback (f.fiberι s)).obj M).presheaf.obj (op ⊤) :=
  colimit.desc _ (fibreSectionCocone f s M)

@[simp]
lemma fibrePushforwardStalkSection_germ (V : S.Opens) (hsV : s ∈ V)
    (τ : Γ(M, f ⁻¹ᵁ V)) :
    fibrePushforwardStalkSection f s M
      (((Scheme.Modules.pushforward f).obj M).presheaf.germ V s hsV τ) =
        fibreNeighbourhoodSection f s M hsV τ := by
  exact ConcreteCategory.congr_hom
    (colimit.ι_desc (fibreSectionCocone f s M) (op ⟨V, hsV⟩)) τ

/-- A fibre section is in the image of the pushforward stalk map exactly when
it lifts over an affine neighbourhood of the base point. -/
lemma mem_range_fibrePushforwardStalkSection_iff
    (σ : GlobalSections ((Scheme.Modules.pullback (f.fiberι s)).obj M)) :
    σ ∈ Set.range (fibrePushforwardStalkSection f s M) ↔
      ∃ (V : S.Opens) (hsV : s ∈ V), IsAffineOpen V ∧
        ∃ τ : Γ(M, f ⁻¹ᵁ V), fibreNeighbourhoodSection f s M hsV τ = σ := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨V, hsV, τ, rfl⟩ :=
      ((Scheme.Modules.pushforward f).obj M).presheaf.exists_germ_eq z
    obtain ⟨W, hW, hsW, hWV⟩ := exists_isAffineOpen_mem_and_subset hsV
    have hle : W ≤ V := hWV
    refine ⟨W, hsW, hW, M.presheaf.map (homOfLE (f.preimage_mono hle)).op τ, ?_⟩
    exact (fibreNeighbourhoodSection_restrict f s M hsV hsW hle τ).trans
      ((fibrePushforwardStalkSection_germ f s M V hsV τ).symm.trans hz)
  · rintro ⟨V, hsV, _, τ, hτ⟩
    refine ⟨((Scheme.Modules.pushforward f).obj M).presheaf.germ V s hsV τ, ?_⟩
    rw [fibrePushforwardStalkSection_germ]
    exact hτ

/-- Surjectivity of the actual pushforward stalk map is equivalent to lifting
all fibre sections on affine neighbourhoods. -/
lemma surjective_fibrePushforwardStalkSection_iff :
    Function.Surjective (fibrePushforwardStalkSection f s M) ↔
      ∀ σ : GlobalSections ((Scheme.Modules.pullback (f.fiberι s)).obj M),
        ∃ (V : S.Opens) (hsV : s ∈ V), IsAffineOpen V ∧
          ∃ τ : Γ(M, f ⁻¹ᵁ V), fibreNeighbourhoodSection f s M hsV τ = σ := by
  exact forall_congr' (mem_range_fibrePushforwardStalkSection_iff f s M)

end Langlands.AlgebraicGeometry.Modules
