import Langlands.AlgebraicGeometry.AffineFppfRefinement
import Langlands.GroupScheme.CocycleRelativeTrivialization

/-! # Cocycle triviality from an affine refinement of the base cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

variable {S : Scheme.{u}} {G : GroupScheme S} {U V : Over S}

set_option backward.isDefEq.respectTransparency false in
/-- Triviality on a refinement that covers the base reflects to the original
cover. The comparison map to the old cover need not be surjective. -/
theorem IsTrivial.of_refine_fpqcCover {ξ : Cocycle G U} (r : V ⟶ U)
    [QuasiCompact V.hom] [Flat V.hom] [Surjective V.hom]
    (hξ : (ξ.refine r).IsTrivial) : ξ.IsTrivial := by
  obtain ⟨f, hf⟩ := hξ
  let P : Over S := Over.mk (𝟙 S)
  let s : V ⟶ P := Over.homMk V.hom
  let : QuasiCompact s.left := by change QuasiCompact V.hom; infer_instance
  let : Flat s.left := by change Flat V.hom; infer_instance
  let : Surjective s.left := by change Surjective V.hom; infer_instance
  obtain ⟨g, hg⟩ := ξ.exists_isTrivialOver r s f (fun a b _ => hf a b)
  let t : U ⟶ U ⊗ P :=
    CartesianMonoidalCategory.lift (𝟙 U) (Over.homMk U.hom)
  refine ⟨t ≫ g, fun {Z} a b => ?_⟩
  have hab : (a ≫ t) ≫ snd U P = (b ≫ t) ≫ snd U P := by
    apply Over.OverMorphism.ext
    simp [t]
  have ht : t ≫ fst U P = 𝟙 U := by simp [t]
  simpa only [Category.assoc, ht, Category.comp_id] using hg (a ≫ t) (b ≫ t) hab

/-- Choose a cochain on the original cover from a coboundary on any refinement
whose structure morphism is fpqc. -/
def fpqcCoverCochain (ξ : Cocycle G U) (r : V ⟶ U)
    [QuasiCompact V.hom] [Flat V.hom] [Surjective V.hom]
    (hξ : (ξ.refine r).IsTrivial) : U ⟶ G.X :=
  Classical.choose (hξ.of_refine_fpqcCover r)

/-- The cochain obtained from a cover of the base has the coboundary equation
on every test scheme. -/
theorem fpqcCoverCochain_spec (ξ : Cocycle G U) (r : V ⟶ U)
    [QuasiCompact V.hom] [Flat V.hom] [Surjective V.hom]
    (hξ : (ξ.refine r).IsTrivial) {Z : Over S} (a b : Z ⟶ U) :
    ξ.toFun a b = (a ≫ ξ.fpqcCoverCochain r hξ) *
      (b ≫ ξ.fpqcCoverCochain r hξ)⁻¹ :=
  Classical.choose_spec (hξ.of_refine_fpqcCover r) a b

/-- Base-cover refinement preserves and reflects cocycle triviality. -/
theorem isTrivial_refine_fpqcCover_iff (ξ : Cocycle G U) (r : V ⟶ U)
    [QuasiCompact V.hom] [Flat V.hom] [Surjective V.hom] :
    (ξ.refine r).IsTrivial ↔ ξ.IsTrivial :=
  ⟨fun h => h.of_refine_fpqcCover r, fun h => h.refine r⟩

set_option backward.isDefEq.respectTransparency false in
/-- On an affine base, vanishing on affine single fppf covers implies vanishing
on all single fppf covers. -/
theorem isTrivial_of_affine_fppf (ξ : Cocycle G U) [IsAffine S]
    [Flat U.hom] [Surjective U.hom] [LocallyOfFinitePresentation U.hom]
    (hG : ∀ (W : Over S) [IsAffine W.left] [Flat W.hom]
      [Surjective W.hom] [LocallyOfFinitePresentation W.hom],
      ∀ ζ : Cocycle G W, ζ.IsTrivial) :
    ξ.IsTrivial := by
  let R := Langlands.AlgebraicGeometry.affineFppfRefinement U
  let : IsAffine R.cover.left := R.isAffine
  let : Flat R.cover.hom := R.flat
  let : Surjective R.cover.hom := R.surjective
  let : LocallyOfFinitePresentation R.cover.hom := R.locallyOfFinitePresentation
  exact (hG R.cover (ξ.refine R.map)).of_refine_fpqcCover R.map

end Langlands.GroupScheme.Cocycle
