import Langlands.AlgebraicGeometry.Picard.FieldPicardDiagonalImmersion
import Langlands.AlgebraicGeometry.AlgebraicSpace.FieldGroupClosedDiagonal
import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasIsoTransport
import Langlands.AlgebraicGeometry.Picard.FieldPicardSheafAlgebraicSpaceStatement
import Langlands.AlgebraicGeometry.Picard.FieldPicardAtlasAssembly

/-! # Closedness of the actual Picard diagonal from class loci and an atlas -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open AlgebraicSpace RelativePicard

/-- Actual class equalizer immersions and a locally finite type etale-surjective
atlas make the full fppf Picard diagonal a closed immersion over any field. -/
theorem fieldPicardDiagonal_isClosedImmersion_of_classEqualizers
    (h : FieldPicardClassEqualizerImmersionStatement.{u})
    (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
    (hX : IsProper X.hom) {U : Over (Spec (CommRingCat.of k))}
    (a : (schemeYoneda _).obj U ⟶ classSheafPresheaf X.hom)
    (ha : IsEtale a) (hs : IsSurjective a) [LocallyOfFiniteType U.hom] :
    AlgebraicSpace.IsClosedImmersion (diag (classSheafPresheaf X.hom)) := by
  have : MorphismProperty.RespectsIso @IsImmersion.{u} :=
    IsImmersion.isStableUnderBaseChange.respectsIso
  let e := forgetSheafIso X.hom
  have hd := relative_diag_of_iso @IsImmersion.{u} e.symm
    (fieldPicardDiagonal_isImmersion_of_classEqualizers h k X hX)
  have hc := GroupIdentity.isClosedImmersion_diag_of_etale_field_atlas
    (sheafPresheaf X.hom) hd (a ≫ e.inv) (ha.comp_iso e.symm) (hs.comp_iso e.symm)
  exact isClosedImmersion_diag_of_iso e.symm hc

/-- A chosen actual closed equalizer locus for any two sections of the Picard
sheaf, under the class-locus and atlas inputs. -/
def fieldPicardSectionClosedEqualizer
    (h : FieldPicardClassEqualizerImmersionStatement.{u})
    (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
    (hX : IsProper X.hom) {U : Over (Spec (CommRingCat.of k))}
    (a : (schemeYoneda _).obj U ⟶ classSheafPresheaf X.hom)
    (ha : IsEtale a) (hs : IsSurjective a) [LocallyOfFiniteType U.hom]
    {T : Over (Spec (CommRingCat.of k))}
    (x y : (classSheafPresheaf X.hom).obj (op T)) :
    Σ (Z : Over (Spec (CommRingCat.of k))),
      {ι : Z ⟶ T // RepresentsEqualizer (F := classSheafPresheaf X.hom) ι x y ∧
        _root_.AlgebraicGeometry.IsClosedImmersion ι.left} := by
  let hex := exists_representsEqualizer_of_relative_diag
    (fieldPicardDiagonal_isClosedImmersion_of_classEqualizers h k X hX a ha hs) x y
  exact ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec⟩

/-- The two geometric inputs suffice for the exact proper-field Picard target;
this lemma retains both inputs explicitly. -/
theorem fieldPicardSheafAlgebraicSpace_of_classEqualizers_of_etale_atlases
    (h : FieldPicardClassEqualizerImmersionStatement.{u})
    (hA : ∀ (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k))),
      IsProper X.hom → ∃ (U : Over (Spec (CommRingCat.of k)))
        (a : (schemeYoneda _).obj U ⟶ classSheafPresheaf X.hom),
        IsEtale a ∧ IsSurjective a ∧ LocallyOfFiniteType U.hom) :
    FieldPicardSheafAlgebraicSpaceStatement.{u} := by
  intro k hk X hX
  obtain ⟨U, a, ha, hs, hU⟩ := hA k X hX
  let : LocallyOfFiniteType U.hom := hU
  have hd := fieldPicardDiagonal_isImmersion_of_classEqualizers h k X hX
  have hc := fieldPicardDiagonal_isClosedImmersion_of_classEqualizers h k X hX a ha hs
  exact ⟨⟨hd.rep, U, a, ha, hs⟩, hc, U, a, ha, hs, hU⟩

/-- The exact target reduces to the four remaining geometric propositions,
with fpqc descent and smooth relative automorphisms already discharged. -/
theorem fieldPicardSheafAlgebraicSpace_of_stackInputs
    (h : FieldPicardClassEqualizerImmersionStatement.{u})
    (hA : FieldPicardStackAtlasStatement.{u})
    (hQ : SmoothAutomorphismEtaleAtlasStatement.{u})
    (hT : FieldEtaleFppfClassSheafStatement.{u}) :
    FieldPicardSheafAlgebraicSpaceStatement.{u} :=
  fieldPicardSheafAlgebraicSpace_of_classEqualizers_of_etale_atlases h
    fun k _ X hX ↦ (fieldPicardAlgebraicSpaceAtlas_of_stackInputs hA hQ hT k X hX).2

end Langlands.AlgebraicGeometry.Picard
