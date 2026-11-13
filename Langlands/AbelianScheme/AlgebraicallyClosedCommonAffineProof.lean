import Langlands.GroupScheme.TranslationLaws
import Langlands.AbelianScheme.AlgebraicallyClosedCommonAffineStatement
import Langlands.AbelianScheme.SeparatingLineBundle.RationalPoints
import Langlands.AlgebraicGeometry.Picard.GeometricPicardZero

/-! # Common affine neighbourhoods by translation -/

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.GroupScheme


/-- Two closed points have a common affine open, by choosing a common translation
parameter for an affine open and using commutativity on rational sections. -/
theorem algebraicallyClosedCommonAffine : AlgebraicallyClosedCommonAffineStatement.{u} := by
  intro K _ _ G _ hsmooth hproper hconnected x y hx hy
  have : Smooth G.X.hom := hsmooth
  have : IsProper G.X.hom := hproper
  have : GeometricallyConnected G.X.hom := hconnected
  have : IrreducibleSpace G.X.left :=
    SeparatingLineBundle.irreducibleSpace_of_smooth_of_isProper G
  let c : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  let x' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X :=
    Over.homMk (pointOfClosedPoint G.X.hom x hx) (pointOfClosedPoint_comp G.X.hom x hx)
  let y' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X :=
    Over.homMk (pointOfClosedPoint G.X.hom y hy) (pointOfClosedPoint_comp G.X.hom y hy)
  have hx' : x'.left c = x := pointOfClosedPoint_apply G.X.hom x hx c
  have hy' : y'.left c = y := pointOfClosedPoint_apply G.X.hom y hy c
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  let p : Bool → (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :=
    fun b ↦ if b then x' else y'
  let V : Bool → G.X.left.Opens := fun b ↦ (translation G (p b)).left ⁻¹ᵁ U
  have hne : ∀ b, (V b : Set G.X.left).Nonempty := by
    intro b
    let e := (Over.forget _).mapIso (CommonAffine.translationIso G (p b))
    obtain ⟨z, hz⟩ := (Scheme.homeoOfIso e).surjective x
    refine ⟨z, ?_⟩
    change (translation G (p b)).left z ∈ U
    change (translation G (p b)).left z = x at hz
    rwa [hz]
  obtain ⟨s, hs, hsV⟩ := SeparatingLineBundle.exists_rationalPoint_mem_of_isOpen
    G.X.hom (fun b ↦ (V b : Set G.X.left)) (fun b ↦ (V b).isOpen) hne
  let s' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X := Over.homMk s hs
  have : IsIso (translation G s').left :=
    ((Over.forget _).mapIso (CommonAffine.translationIso G s')).isIso_hom
  refine ⟨(translation G s').left ⁻¹ᵁ U, hU.preimage_of_isIso _, ?_, ?_⟩
  · change (translation G s').left x ∈ U
    rw [← hx', CommonAffine.translation_apply_section G s' x']
    exact hsV true
  · change (translation G s').left y ∈ U
    rw [← hy', CommonAffine.translation_apply_section G s' y']
    exact hsV false

end Langlands.GroupScheme
