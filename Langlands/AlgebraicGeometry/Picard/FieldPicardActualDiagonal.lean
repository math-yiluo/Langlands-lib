import Langlands.AlgebraicGeometry.Picard.TrivialLocusNoetherian
import Langlands.AlgebraicGeometry.Picard.FieldPicardClosedDiagonal

/-! # The actual Picard diagonal over an arbitrary field -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open AlgebraicSpace RelativePicard

/-- A chosen immersed equality locus for arbitrary sections of the actual fppf
Picard sheaf of a proper scheme over any field. -/
def fieldPicardImmersedEqualizer
    (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
    (hX : IsProper X.hom) {T : Over (Spec (CommRingCat.of k))}
    (x y : (classSheafPresheaf X.hom).obj (op T)) :
    Σ (Z : Over (Spec (CommRingCat.of k))),
      {ι : Z ⟶ T // RepresentsEqualizer (F := classSheafPresheaf X.hom) ι x y ∧
        IsImmersion ι.left} :=
  fieldPicardSectionEqualizer fieldPicardClassEqualizerImmersion k X hX x y

/-- The full diagonal of the actual fppf Picard sheaf of a proper scheme over
any field is representable by immersions. -/
theorem fieldPicardDiagonal_isImmersion
    (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
    (hX : IsProper X.hom) :
    (MorphismProperty.inverseImage @IsImmersion.{u} (Over.forget _)).relative
      (schemeYoneda _) (diag (classSheafPresheaf X.hom)) :=
  fieldPicardDiagonal_isImmersion_of_classEqualizers
    fieldPicardClassEqualizerImmersion k X hX

/-- A locally finite type etale-surjective atlas upgrades the actual Picard
diagonal to a closed immersion; class-equalizer existence is discharged. -/
theorem fieldPicardDiagonal_isClosedImmersion_of_etale_atlas
    (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
    (hX : IsProper X.hom) {U : Over (Spec (CommRingCat.of k))}
    (a : (schemeYoneda _).obj U ⟶ classSheafPresheaf X.hom)
    (ha : IsEtale a) (hs : IsSurjective a) [LocallyOfFiniteType U.hom] :
    AlgebraicSpace.IsClosedImmersion (diag (classSheafPresheaf X.hom)) :=
  fieldPicardDiagonal_isClosedImmersion_of_classEqualizers
    fieldPicardClassEqualizerImmersion k X hX a ha hs

end Langlands.AlgebraicGeometry.Picard
