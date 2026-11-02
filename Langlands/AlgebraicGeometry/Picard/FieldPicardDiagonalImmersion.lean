import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfLocalEqualizer
import Langlands.AlgebraicGeometry.Picard.FieldPicardClassEqualizerImmersionStatement
import Langlands.AlgebraicGeometry.Picard.RelativePicardLocalRepresentatives

/-! # From actual line-bundle class loci to the full Picard diagonal -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open AlgebraicSpace RelativePicard

/-- Class equalizer immersions for actual bundles suffice for arbitrary sections
of the actual fppf Picard sheaf, including sections without global representatives. -/
theorem exists_fieldPicardSectionEqualizer
    (h : FieldPicardClassEqualizerImmersionStatement.{u})
    (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
    (hX : IsProper X.hom) {T : Over (Spec (CommRingCat.of k))}
    (x y : (classSheafPresheaf X.hom).obj (op T)) :
    ∃ (Z : Over (Spec (CommRingCat.of k))) (ι : Z ⟶ T),
      RepresentsEqualizer (F := classSheafPresheaf X.hom) ι x y ∧ IsImmersion ι.left := by
  apply exists_representsEqualizer_of_fppf_local (classSheafPresheaf_isSheaf X.hom) x y
    (representativeSieve X.hom T x ⊓ representativeSieve X.hom T y)
    (commonRepresentativeSieve_mem X.hom T x y)
  intro V g hg
  let L := localRepresentative X.hom x g hg.1
  let M := localRepresentative X.hom y g hg.2
  obtain ⟨Z, ι, hι, hrep⟩ := h k X hX V L M
  refine ⟨Z, ι, hι, ?_⟩
  have hL := localRepresentative_spec X.hom x g hg.1
  have hM := localRepresentative_spec X.hom y g hg.2
  dsimp [L, M] at hrep
  rwa [hL, hM] at hrep

/-- The chosen actual immersed equalizer locus for any two sheaf sections. -/
def fieldPicardSectionEqualizer
    (h : FieldPicardClassEqualizerImmersionStatement.{u})
    (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
    (hX : IsProper X.hom) {T : Over (Spec (CommRingCat.of k))}
    (x y : (classSheafPresheaf X.hom).obj (op T)) :
    Σ (Z : Over (Spec (CommRingCat.of k))),
      {ι : Z ⟶ T // RepresentsEqualizer (F := classSheafPresheaf X.hom) ι x y ∧
        IsImmersion ι.left} :=
  let hex := exists_fieldPicardSectionEqualizer h k X hX x y
  ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec⟩

/-- The full Picard diagonal is representable by immersions from the actual
bundle-class equalizer input. -/
theorem fieldPicardDiagonal_isImmersion_of_classEqualizers
    (h : FieldPicardClassEqualizerImmersionStatement.{u})
    (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
    (hX : IsProper X.hom) :
    (MorphismProperty.inverseImage @IsImmersion.{u} (Over.forget _)).relative
      (schemeYoneda _) (diag (classSheafPresheaf X.hom)) :=
  relative_isImmersion_diag_of_representsEqualizer fun _ x y ↦
    exists_fieldPicardSectionEqualizer h k X hX x y

end Langlands.AlgebraicGeometry.Picard
