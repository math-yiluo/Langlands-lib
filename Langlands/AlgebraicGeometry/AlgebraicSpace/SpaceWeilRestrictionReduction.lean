import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeWeilRestrictionComparison
import Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionGeometricInputsStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceProductPointsSurjective
import Mathlib.AlgebraicGeometry.Morphisms.Descent
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Affine atlas construction and assembly for restriction of scalars -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open PointTopology

set_option backward.isDefEq.respectTransparency false

/-- Refine a quasi-compact structural atlas to an affine one, retaining any structural
property stable under composition and implied by étaleness. -/
theorem HasAtlasProperty.exists_affine_atlas
    {S : Scheme.{u}} [CompactSpace S] {X : AlgebraicSpace S}
    (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderComposition] (hEP : @Etale.{u} ≤ P)
    (hX : HasAtlasProperty (P ⊓ @QuasiCompact.{u}) X) :
    ∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf),
      IsAffine U.left ∧ IsEtale a ∧ IsSurjective a ∧ P U.hom := by
  obtain ⟨W, a, ha, hs, hW⟩ := hX
  have : QuasiCompact W.hom := hW.2
  have : CompactSpace W.left := QuasiCompact.compactSpace_of_compactSpace W.hom
  let : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u})
  let : MorphismProperty.ContainsIdentities @Etale.{u} :=
    ⟨fun T => inferInstanceAs (Etale (𝟙 T))⟩
  obtain ⟨V, j, hjS, hjE, hV⟩ :=
    Scheme.exists_hom_isAffine_of_isZariskiLocalAtSource (@Etale.{u}) W.left
  let U : Over S := Over.mk (j ≫ W.hom)
  let j' : U ⟶ W := Over.homMk j
  refine ⟨U, (schemeYoneda S).map j' ≫ a, hV, (isEtale_map j' hjE).comp ha,
    SpaceProductPoints.IsSurjective.comp (SpaceProductPoints.isSurjective_map j' hjS) hs, ?_⟩
  exact P.comp_mem j W.hom (hEP _ _ j hjE) hW.1

/-- The coordinate algebra of an affine locally finitely presented scheme has the same
finite-presentation property. -/
theorem affineCoordinate_finitePresentation
    (R : Type u) [CommRing R] (U : Over (Spec (CommRingCat.of R)))
    [IsAffine U.left] [LocallyOfFinitePresentation U.hom] :
    Algebra.FinitePresentation R (AffineCoordinateRing R U) := by
  rw [← RingHom.finitePresentation_algebraMap]
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)
    (Q := @RingHom.FinitePresentation)
    (φ := CommRingCat.ofHom (algebraMap R (AffineCoordinateRing R U)))).mp
  change LocallyOfFinitePresentation (Spec.algebraMap R (AffineCoordinateRing R U))
  rw [affineCoordinateSpecMap]
  infer_instance

/-- The existing affine finite-type Weil algebra is finitely presented whenever the
original affine scheme is locally finitely presented. -/
theorem affineWeilRestriction_locallyOfFinitePresentation
    (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
    [Module.Finite R R'] [Module.Projective R R']
    (U : Over (Spec (CommRingCat.of R'))) [IsAffine U.left]
    [LocallyOfFinitePresentation U.hom] :
    LocallyOfFinitePresentation (affineWeilRestriction R R' U).hom := by
  let : Algebra.FinitePresentation R' (AffineCoordinateRing R' U) :=
    affineCoordinate_finitePresentation R' U
  let : Algebra.FinitePresentation R
      (Langlands.Algebra.WeilRestrictionFiniteType R R' (AffineCoordinateRing R' U)) :=
    Algebra.FinitePresentation.equiv
      (Langlands.Algebra.WeilRestrictionFiniteType.finitePresentationAlgEquiv R R'
        (AffineCoordinateRing R' U)).symm
  apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

variable (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
  [Module.Finite R R'] [Module.Projective R R']
  (X' : AlgebraicSpace (Spec (CommRingCat.of R')))
  (U' : Over (Spec (CommRingCat.of R'))) [IsAffine U'.left]
  [LocallyOfFiniteType U'.hom]

/-- The actual map from the affine Weil scheme to the sheaf restriction induced by a
scheme chart of the original space. -/
def restrictedAffineAtlas (a : (schemeYoneda _).obj U' ⟶ X'.presheaf) :
    (schemeYoneda _).obj (affineWeilRestriction R R' U') ⟶
      ((ringWeilRestriction R R').obj X'.toSheaf).obj :=
  (affineWeilRestrictionPresheafIso R R' U').hom ≫
    Functor.whiskerLeft (Over.pullback (Spec.algebraMap R R')).op a

/-- Étaleness and surjectivity of the restricted full-presheaf map transfer to its
actual affine representing scheme. -/
theorem restrictedAffineAtlas_properties
    (a : (schemeYoneda _).obj U' ⟶ X'.presheaf)
    (he : IsEtale (Functor.whiskerLeft (Over.pullback (Spec.algebraMap R R')).op a))
    (hs : IsSurjective
      (Functor.whiskerLeft (Over.pullback (Spec.algebraMap R R')).op a)) :
    IsEtale (restrictedAffineAtlas R R' X' U' a) ∧
      IsSurjective (restrictedAffineAtlas R R' X' U' a) := by
  constructor
  · exact (MorphismProperty.cancel_left_of_respectsIso
      ((MorphismProperty.inverseImage (@Etale.{u}) (Over.forget _)).relative
        (schemeYoneda _)) _ _).mpr he
  · exact (MorphismProperty.cancel_left_of_respectsIso
      ((MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget _)).relative
        (schemeYoneda _)) _ _).mpr hs

/-- The unchanged full Lemma 5.10 follows from the two isolated geometric inputs.
Finite type and finite presentation are obtained from actual affine atlases. -/
theorem spaceWeilRestriction_of_geometricInputs
    (hD : WeilRestrictionDiagonalStatement.{u})
    (hA : WeilRestrictionAffineEtaleAtlasStatement.{u}) :
    SpaceWeilRestrictionStatement.{u} := by
  intro R R' _ _ _ _ _ X' hqs hft
  obtain ⟨U, a, hU, ha, hs, hftU⟩ :=
    HasAtlasProperty.exists_affine_atlas (@LocallyOfFiniteType.{u})
      (fun _ _ f hf => by let := hf; infer_instance) hft
  let := hU
  let := hftU
  obtain ⟨he, hsurj⟩ := hA R R' X' hqs U a ha hs
  obtain ⟨he', hsurj'⟩ := restrictedAffineAtlas_properties R R' X' U a he hsurj
  obtain ⟨hdiag, hsep⟩ := hD R R' X' hqs
  let h : IsAlgebraicSpace _ ((ringWeilRestriction R R').obj X'.toSheaf) :=
    ⟨hdiag.1, affineWeilRestriction R R' U, restrictedAffineAtlas R R' X' U a, he', hsurj'⟩
  refine ⟨h, hdiag, ?_, hsep, ?_⟩
  · exact ⟨affineWeilRestriction R R' U, restrictedAffineAtlas R R' X' U a,
      he', hsurj', inferInstance, affineWeilRestriction_quasiCompact R R' U⟩
  · intro hfp
    obtain ⟨V, b, hV, hb, ht, hfpV⟩ :=
      HasAtlasProperty.exists_affine_atlas (@LocallyOfFinitePresentation.{u})
        (fun _ _ f hf => by let := hf; infer_instance) hfp
    let := hV
    let := hfpV
    obtain ⟨heV, hsV⟩ := hA R R' X' hqs V b hb ht
    obtain ⟨heV', hsV'⟩ := restrictedAffineAtlas_properties R R' X' V b heV hsV
    exact ⟨affineWeilRestriction R R' V, restrictedAffineAtlas R R' X' V b,
      heV', hsV', affineWeilRestriction_locallyOfFinitePresentation R R' V,
      affineWeilRestriction_quasiCompact R R' V⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
