import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Affine refinements of single fppf covers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

variable {S : Scheme.{u}}

/-- A single affine fppf cover of the base factoring through the supplied cover.
The comparison map itself need not cover the old total space. -/
structure AffineFppfRefinement (U : Over S) where
  cover : Over S
  map : cover ⟶ U
  isAffine : IsAffine cover.left
  flat : Flat cover.hom
  surjective : Surjective cover.hom
  locallyOfFinitePresentation : LocallyOfFinitePresentation cover.hom

set_option backward.isDefEq.respectTransparency false in
/-- A single fppf cover of a quasi-compact scheme has an affine fppf refinement. -/
theorem nonempty_affineFppfRefinement (U : Over S) [CompactSpace S]
    [Flat U.hom] [Surjective U.hom] [LocallyOfFinitePresentation U.hom] :
    Nonempty (AffineFppfRefinement U) := by
  classical
  let P : MorphismProperty Scheme.{u} := @Flat ⊓ @LocallyOfFinitePresentation
  let : P.RespectsLeft @IsOpenImmersion := by
    dsimp [P]
    infer_instance
  let 𝒰 := U.hom.cover (P := P) ⟨inferInstance, inferInstance⟩
  have : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap fun _ => U.hom.isOpenMap
  obtain ⟨𝒱, f, hfin, _⟩ := QuasiCompactCover.exists_hom.{u} 𝒰
  let : Finite 𝒱.I₀ := hfin
  let W : Scheme.{u} := ∐ (fun j : 𝒱.I₀ => Spec (𝒱.X j))
  let p : W ⟶ S := Sigma.desc 𝒱.f
  let r : W ⟶ U.left := Sigma.desc fun j => f.h₀ j
  have hr : r ≫ U.hom = p := by
    apply Sigma.hom_ext
    intro j
    simpa [r, p, 𝒰] using f.w₀ j
  have hp : P p := IsZariskiLocalAtSource.sigmaDesc 𝒱.map_prop
  have hs : Surjective p := inferInstanceAs (Surjective (Sigma.desc 𝒱.cover.f))
  exact ⟨{
    cover := Over.mk p
    map := Over.homMk r hr
    isAffine := by
      change IsAffine W
      dsimp [W]
      infer_instance
    flat := hp.1
    surjective := hs
    locallyOfFinitePresentation := hp.2 }⟩

/-- Choose an affine fppf refinement without a quasi-compactness condition on
its original total space. -/
def affineFppfRefinement (U : Over S) [CompactSpace S]
    [Flat U.hom] [Surjective U.hom] [LocallyOfFinitePresentation U.hom] :
    AffineFppfRefinement U :=
  Classical.choice (nonempty_affineFppfRefinement U)

end Langlands.AlgebraicGeometry
