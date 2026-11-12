import Langlands.AlgebraicGeometry.Picard.NormalFiniteTypeAbelianAmpleExistenceStatement
import Langlands.AlgebraicGeometry.Picard.NoetherianAffineAbelianGenericAmpleStatement
import Langlands.AlgebraicGeometry.Picard.NormalModelTwoAxisExtensionReduction
import Langlands.AlgebraicGeometry.Picard.FieldAmpleDiagonalCorrespondenceProof
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof
import Langlands.AbelianScheme.FieldAmpleExistenceProof

/-! # Normal-base ample existence from two explicit geometric inputs -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AbelianScheme

set_option backward.isDefEq.respectTransparency false in
/-- Two-axis extension constructs an actual total line bundle with ample
canonical generic restriction, assuming normal two-axis extension. -/
theorem normalFiniteTypeAbelian_exists_genericallyAmple_of_twoAxis
    (extension : NormalFiniteTypeTwoAxisExtensionProperty.{u})
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra.FiniteType ℤ R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))) :
    ∃ L : LineBundle A.X.left,
      ((LineBundle.pullback (pullback.fst A.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))).obj L).IsAmple := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let B := (baseChange b).obj A
  let π := pullback.fst A.X.hom b
  have hAmple : ∃ L : LineBundle B.X.left, L.IsAmple :=
    Langlands.GroupScheme.fieldAmpleExistence (FractionRing R) B.toGrp
      inferInstance inferInstance inferInstance
  obtain ⟨D, hFirst, hSecond, hDiagonal⟩ :=
    fieldAmpleDiagonalCorrespondence (FractionRing R) B hAmple
  obtain ⟨E, ⟨e⟩⟩ := extension R A D hFirst hSecond
  refine ⟨(LineBundle.pullback (pullback.diagonal A.X.hom)).obj E, ?_⟩
  let q := pullback.map B.X.hom B.X.hom A.X.hom A.X.hom
    π π b pullback.condition.symm pullback.condition.symm
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

/-- Normal two-axis extension and the generic ampleness criterion suffice for
the exact unconditional existence target; neither premise is discharged here. -/
theorem normalFiniteTypeAbelianAmpleExistence_of_twoAxis_genericAmple
    (extension : NormalFiniteTypeTwoAxisExtensionProperty.{u})
    (genericAmple : NoetherianAffineAbelianGenericAmpleStatement.{u}) :
    NormalFiniteTypeAbelianAmpleExistenceStatement.{u} := by
  intro R _ _ _ _ A
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  obtain ⟨L, hL⟩ := normalFiniteTypeAbelian_exists_genericallyAmple_of_twoAxis extension R A
  exact ⟨L, genericAmple R A L hL⟩

end Langlands.AlgebraicGeometry.Picard
