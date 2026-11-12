import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldTranslationDifferenceLiftingStatement
import Langlands.AlgebraicGeometry.Picard.FieldTwistedMumfordFibreRestrictionProof
import Langlands.AlgebraicGeometry.Picard.TranslationInvariantCohomologyVanishingProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleTranslationStabilizerFiniteProof
import Langlands.AlgebraicGeometry.Picard.SquareFirstProjectionAcyclicityProof
import Langlands.AlgebraicGeometry.Picard.SquareSecondProjectionFiniteSupportDetectionProof
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoClassGroup
import Langlands.AbelianScheme.FieldCubePullbackProof

/-! # Translation-difference lifting over algebraically closed fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The trivial line bundle has nonzero degree-zero cohomology on a scheme
with a rational section over a field. -/
private theorem not_isZero_trivial_h0
    (K : Type u) [Field K] (X : Over (Spec (CommRingCat.of K)))
    (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X) :
    ¬ IsZero ((relativeCohomology X.hom 0).obj (LineBundle.trivial X.left).obj) := by
  intro h
  have hΓ := h.of_iso
    (((relativeCohomologyZeroIso X.hom).app (structureSheaf X.left) ≪≫
      ((relativeGlobalSectionsIso X.hom).app (structureSheaf X.left)).symm).symm)
  have : Subsingleton Γ(X.left, ⊤) := ModuleCat.subsingleton_of_isZero hΓ
  have h10 : (1 : Γ(X.left, ⊤)) = 0 := Subsingleton.elim _ _
  let φ : Γ(X.left, ⊤) ⟶ CommRingCat.of K :=
    x.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom
  exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrArg φ.hom h10)

/-- The two-projection argument, with the balanced cube as an explicit input. -/
theorem algClosedFieldTranslationDifferenceLifting_of_cube
    (cube : Langlands.GroupScheme.FieldCubePullbackStatement.{u}) :
    AlgClosedFieldTranslationDifferenceLiftingStatement.{u} := by
  classical
  intro preservation K _ _ A L N evaluation P hL hP
  by_contra hNoLift
  obtain ⟨R, ⟨evaluationP⟩⟩ := LineBundle.exists_tensorObj_iso_structureSheaf P
  let D (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) : LineBundle A.X.left :=
    LineBundle.tensor preservation
      ((LineBundle.pullback (GroupScheme.translation A.toGrp x).left).obj L) N
  have hD (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) :
      GroupScheme.IsTranslationInvariant A.toGrp (D x) :=
    MumfordPicardZero.isTranslationInvariant_square preservation cube
      fieldLineBundleTriviality A x L N evaluation
  have hR : GroupScheme.IsTranslationInvariant A.toGrp R :=
    GroupScheme.isTranslationInvariant_tensorInverse preservation A.toGrp evaluationP hP
  have hEval : LineBundle.isoClass preservation L * LineBundle.isoClass preservation N = 1 :=
    LineBundle.isoClass_eq_of_iso (ObjectProperty.isoMk _ evaluation)
  have hEvalP : LineBundle.isoClass preservation P * LineBundle.isoClass preservation R = 1 :=
    LineBundle.isoClass_eq_of_iso (ObjectProperty.isoMk _ evaluationP)
  let Z : Scheme.{u} := pullback A.X.hom A.X.hom
  let Q : LineBundle Z :=
    LineBundle.tensor preservation
      (LineBundle.tensor preservation
        (LineBundle.tensor preservation
          ((LineBundle.pullback (mumfordAddition A)).obj L)
          ((LineBundle.pullback (pullback.fst A.X.hom A.X.hom)).obj N))
        ((LineBundle.pullback (pullback.snd A.X.hom A.X.hom)).obj N))
      ((LineBundle.pullback (pullback.snd A.X.hom A.X.hom)).obj R)
  have hTotal : ∀ n : ℕ,
      IsZero ((relativeCohomology (pullback.fst A.X.hom A.X.hom ≫ A.X.hom) n).obj Q.obj) := by
    apply algClosedFieldSquareFirstProjectionAcyclicity K A Q
    intro x n
    obtain ⟨e⟩ := (fieldTwistedMumfordFibreRestriction preservation K A L N R x).1
    have hNontrivial : ¬ Nonempty
        (LineBundle.tensor preservation (D x) R ≅ LineBundle.trivial A.X.left) := by
      rintro ⟨d⟩
      have hd : LineBundle.isoClass preservation (D x) * LineBundle.isoClass preservation R = 1 :=
        LineBundle.isoClass_eq_of_iso d
      exact hNoLift ⟨x, LineBundle.isoClass_eq_iff.mp
        (mul_right_cancel (hd.trans hEvalP.symm))⟩
    exact (algClosedFieldTranslationInvariantCohomologyVanishing K A _
      (GroupScheme.isTranslationInvariant_tensor preservation A.toGrp (hD x) hR)
      hNontrivial n).of_iso
      ((relativeCohomology A.X.hom n).mapIso ((LineBundle.forget _).mapIso e))
  let F : Set (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) :=
    {x | Nonempty ((LineBundle.pullback (GroupScheme.translation A.toGrp x).left).obj L ≅ L)}
  have hF : F.Finite :=
    Set.finite_coe_iff.mp (algClosedFieldAmpleTranslationStabilizerFinite K A L hL)
  have hAll := algClosedFieldSquareSecondProjectionFiniteSupportDetection K A Q F hF
    (by
      intro x hx n
      obtain ⟨e⟩ := (fieldTwistedMumfordFibreRestriction preservation K A L N R x).2
      have hNontrivial : ¬ Nonempty (D x ≅ LineBundle.trivial A.X.left) := by
        rintro ⟨d⟩
        have hd : LineBundle.isoClass preservation
            ((LineBundle.pullback (GroupScheme.translation A.toGrp x).left).obj L) *
            LineBundle.isoClass preservation N = 1 := LineBundle.isoClass_eq_of_iso d
        exact hx (LineBundle.isoClass_eq_iff.mp (mul_right_cancel (hd.trans hEval.symm)))
      exact (algClosedFieldTranslationInvariantCohomologyVanishing K A (D x)
        (hD x) hNontrivial n).of_iso
        ((relativeCohomology A.X.hom n).mapIso ((LineBundle.forget _).mapIso e))) hTotal
  let origin : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X := 1
  obtain ⟨eOrigin⟩ := (fieldTwistedMumfordFibreRestriction preservation K A L N R origin).2
  have hDOrigin : Nonempty (D origin ≅ LineBundle.trivial A.X.left) := by
    apply LineBundle.isoClass_eq_iff.mp
    change LineBundle.pullbackHom preservation (GroupScheme.translation A.toGrp origin).left
      (LineBundle.isoClass preservation L) * LineBundle.isoClass preservation N = 1
    simpa only [origin, GroupScheme.translation_one, Over.id_left, LineBundle.pullbackHom_id]
      using hEval
  obtain ⟨dOrigin⟩ := hDOrigin
  have hZero : IsZero
      ((relativeCohomology A.X.hom 0).obj (LineBundle.trivial A.X.left).obj) :=
    (hAll origin 0).of_iso
      ((relativeCohomology A.X.hom 0).mapIso
        ((LineBundle.forget _).mapIso (eOrigin ≪≫ dOrigin))).symm
  exact not_isZero_trivial_h0 K A.X origin hZero

/-- Every translation-invariant line bundle is a translation difference of an
ample line bundle over an algebraically closed field. -/
theorem algClosedFieldTranslationDifferenceLifting :
    AlgClosedFieldTranslationDifferenceLiftingStatement.{u} :=
  algClosedFieldTranslationDifferenceLifting_of_cube
    Langlands.GroupScheme.fieldCubePullback.{u}

end Langlands.AbelianScheme
