import Langlands.AlgebraicGeometry.Picard.PointFiberIsomScheme
import Langlands.AlgebraicGeometry.Picard.ProperLineBundleIsomRepresentabilityProof
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Affine product representations of actual Picard point fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- Every actual point fibre has a scheme representation affine and locally
finitely presented over the product of the two parameter schemes. -/
def HasAffinePointFiberSchemes : Prop :=
  ∀ (U T : Over S)
    (L : LineBundle ((relativeSpace f).obj U))
    (M : LineBundle ((relativeSpace f).obj T)),
    ∃ I : Over (U ⨯ T).left,
      Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj (Stacks.pointFiberScheme I) ≅
        pointFiberPresheaf f L M) ∧
      IsAffineHom I.hom ∧ LocallyOfFinitePresentation I.hom

/-- The published focused Isom theorem represents every actual point fibre. -/
theorem hasAffinePointFiberSchemes
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] :
    HasAffinePointFiberSchemes f := by
  intro U T L M
  exact exists_pointFiberIsomScheme_of_properLineBundleIsom f L M
    properLineBundleIsomRepresentability inferInstance inferInstance inferInstance

variable {U T : Over S}
  (L : LineBundle ((relativeSpace f).obj U))
  (M : LineBundle ((relativeSpace f).obj T))

/-- Finite presentation of the parameter scheme gives finite presentation of
the representing point-fibre scheme over the test scheme. -/
theorem exists_locallyOfFinitePresentation_pointFiberScheme
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation U.hom] :
    ∃ I : Over (U ⨯ T).left,
      Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj (Stacks.pointFiberScheme I) ≅
        pointFiberPresheaf f L M) ∧
      IsAffineHom I.hom ∧ LocallyOfFinitePresentation I.hom ∧
      LocallyOfFinitePresentation (Stacks.pointFiberScheme I).hom := by
  obtain ⟨I, e, hI, hIfp⟩ := hasAffinePointFiberSchemes f U T L M
  let : LocallyOfFinitePresentation I.hom := hIfp
  have hprod : IsPullback (prod.fst : U ⨯ T ⟶ U).left
      (prod.snd : U ⨯ T ⟶ T).left U.hom T.hom :=
    Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (prod.fst : U ⨯ T ⟶ U) (prod.snd : U ⨯ T ⟶ T))
      (prodIsProd U T)
  let : LocallyOfFinitePresentation (prod.snd : U ⨯ T ⟶ T).left :=
    MorphismProperty.of_isPullback hprod inferInstance
  refine ⟨I, e, hI, hIfp, ?_⟩
  change LocallyOfFinitePresentation (I.hom ≫ (prod.snd : U ⨯ T ⟶ T).left)
  infer_instance

variable {k : Type u} [Field k] (Y : Over (Spec (CommRingCat.of k)))

/-- A proper scheme over any field has affine product representations of all
actual point fibres, with no additional geometric hypothesis. -/
theorem hasAffinePointFiberSchemes_of_isProper_over_field [IsProper Y.hom] :
    HasAffinePointFiberSchemes Y.hom := by
  exact hasAffinePointFiberSchemes Y.hom

/-- Over any field, local finite type of the parameter and properness of the
source suffice for locally finitely presented point-fibre schemes on all tests. -/
theorem exists_locallyOfFinitePresentation_pointFiberScheme_over_field
    [IsProper Y.hom] {U T : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType U.hom]
    (L : LineBundle ((relativeSpace Y.hom).obj U))
    (M : LineBundle ((relativeSpace Y.hom).obj T)) :
    ∃ I : Over (U ⨯ T).left,
      Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj (Stacks.pointFiberScheme I) ≅
        pointFiberPresheaf Y.hom L M) ∧
      IsAffineHom I.hom ∧ LocallyOfFinitePresentation I.hom ∧
      LocallyOfFinitePresentation (Stacks.pointFiberScheme I).hom := by
  exact exists_locallyOfFinitePresentation_pointFiberScheme Y.hom L M

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
