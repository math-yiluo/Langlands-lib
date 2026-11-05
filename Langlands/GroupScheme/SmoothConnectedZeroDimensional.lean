import Langlands.GroupScheme.IdentityComponent
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Topology.Connected.Clopen

/-! # Connected zero-dimensional smooth groups over a field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry

/-- An étale scheme over a field with connected underlying space and a rational
section is isomorphic to the spectrum of the field. -/
theorem isIso_of_connected_etale_section {k : Type u} [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [Etale p] [ConnectedSpace X]
    (s : Spec (CommRingCat.of k) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    IsIso p := by
  let : MorphismProperty.HasOfPostcompProperty
      @IsOpenImmersion @Etale :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
      fun _ _ _ _ ↦ inferInstanceAs (IsOpenImmersion _)
  have : IsOpenImmersion (s ≫ p) := by rw [hs]; infer_instance
  have : IsOpenImmersion s :=
    MorphismProperty.of_postcomp @IsOpenImmersion (W' := @Etale) s p
      inferInstance inferInstance
  have : IsClosedImmersion s := isClosedImmersion_of_comp_eq_id p s hs
  have hrange : Set.range s = Set.univ :=
    (show IsClopen (Set.range s) from
      ⟨s.isClosedEmbedding.isClosed_range, s.isOpenEmbedding.isOpen_range⟩).eq_univ
        (Set.range_nonempty s)
  have : Epi s.base := (TopCat.epi_iff_surjective _).mpr
    (Set.range_eq_univ.mp hrange)
  have : IsIso s := IsOpenImmersion.isIso s
  have : IsIso (s ≫ p) := by rw [hs]; infer_instance
  exact IsIso.of_isIso_comp_left s p

/-- The isomorphism supplied by a rational section of a connected étale scheme
has the original structure morphism as its forward map. -/
def connectedEtaleSectionIso {k : Type u} [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [Etale p] [ConnectedSpace X]
    (s : Spec (CommRingCat.of k) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    X ≅ Spec (CommRingCat.of k) := by
  let := isIso_of_connected_etale_section p s hs
  exact asIso p

@[simp]
theorem connectedEtaleSectionIso_hom {k : Type u} [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [Etale p] [ConnectedSpace X]
    (s : Spec (CommRingCat.of k) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    (connectedEtaleSectionIso p s hs).hom = p := rfl

end Langlands.AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A connected smooth group of relative dimension zero over any field is
trivial: every homomorphism from it is the zero homomorphism. -/
theorem eq_zero_of_smoothOfRelativeDimension_zero_over_field
    {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [ConnectedSpace G.X.left]
    (f : G ⟶ H) (h0 : SmoothOfRelativeDimension 0 G.X.hom) : f = 0 := by
  have : Etale G.X.hom := (Etale.iff_smoothOfRelativeDimension_zero _).mpr h0
  have : IsIso G.X.hom :=
    Langlands.AlgebraicGeometry.isIso_of_connected_etale_section
      G.X.hom η[G.X].left η[G.X].w
  have hid : (𝟙 G.X : G.X ⟶ G.X) = 1 := by
    apply Over.OverMorphism.ext
    apply (cancel_mono G.X.hom).mp
    exact (Over.w (𝟙 G.X)).trans (Over.w (1 : G.X ⟶ G.X)).symm
  apply (Grp.forget _).map_injective
  change f.hom.hom = 1
  calc
    f.hom.hom = (𝟙 G.X) ≫ f.hom.hom := (Category.id_comp _).symm
    _ = 1 := by rw [hid, MonObj.one_comp]

end Langlands.GroupScheme
