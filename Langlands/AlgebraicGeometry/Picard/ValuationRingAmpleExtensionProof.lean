import Langlands.AlgebraicGeometry.Picard.ValuationRingAmpleExtensionStatement
import Langlands.AlgebraicGeometry.Picard.ValuationRingTwoAxisExtensionProof
import Langlands.AlgebraicGeometry.Picard.FieldAmpleDiagonalCorrespondenceProof
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof

/-! # Ample extension from the generic fibre over a valuation ring -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false in
/-- The actual-bundle diagonal assembly, conditional on the two geometric inputs. -/
theorem valuationRingAmpleExtension_of_twoAxis
    (extension : ValuationRingTwoAxisExtensionStatement.{u})
    (field : FieldAmpleDiagonalCorrespondenceStatement.{u}) :
    ValuationRingAmpleExtensionStatement.{u} := by
  intro R _ _ _ K _ _ _ A hAmple
  let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let B := (baseChange b).obj A
  let π := pullback.fst A.X.hom b
  let q := pullback.map B.X.hom B.X.hom A.X.hom A.X.hom
    π π b pullback.condition.symm pullback.condition.symm
  obtain ⟨D, hFirst, hSecond, hDiagonal⟩ := field K B hAmple
  obtain ⟨E, ⟨e⟩⟩ := extension R K A D hFirst hSecond
  refine ⟨(LineBundle.pullback (pullback.diagonal A.X.hom)).obj E, ?_⟩
  have hSquare : π ≫ pullback.diagonal A.X.hom =
      pullback.diagonal B.X.hom ≫ q := by
    apply pullback.hom_ext
    · dsimp only [q, pullback.map]
      rw [Category.assoc, pullback.diagonal_fst, Category.comp_id,
        Category.assoc, pullback.lift_fst, pullback.diagonal_fst_assoc]
    · dsimp only [q, pullback.map]
      rw [Category.assoc, pullback.diagonal_snd, Category.comp_id,
        Category.assoc, pullback.lift_snd, pullback.diagonal_snd_assoc]
  let comparison :
      (Scheme.Modules.pullback π).obj
          ((Scheme.Modules.pullback (pullback.diagonal A.X.hom)).obj E.obj) ≅
        (Scheme.Modules.pullback (pullback.diagonal B.X.hom)).obj D.obj :=
    (Scheme.Modules.pullbackComp π (pullback.diagonal A.X.hom)).app E.obj ≪≫
      (Scheme.Modules.pullbackCongr hSquare).app E.obj ≪≫
        ((Scheme.Modules.pullbackComp (pullback.diagonal B.X.hom) q).app E.obj).symm ≪≫
          (Scheme.Modules.pullback (pullback.diagonal B.X.hom)).mapIso e
  exact hDiagonal.of_iso comparison.symm

/-- An ample bundle on the generic fibre yields a total bundle with ample generic pullback,
for every valuation domain and every supplied fraction field. -/
theorem valuationRingAmpleExtension : ValuationRingAmpleExtensionStatement.{u} :=
  valuationRingAmpleExtension_of_twoAxis.{u}
    valuationRingTwoAxisExtension.{u} fieldAmpleDiagonalCorrespondence.{u}

end Langlands.AbelianScheme
