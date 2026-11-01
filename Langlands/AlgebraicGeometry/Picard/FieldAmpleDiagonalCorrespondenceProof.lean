import Langlands.AlgebraicGeometry.Picard.FieldAmpleDiagonalCorrespondenceStatement
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation
import Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof
import Langlands.AlgebraicGeometry.Picard.AmpleTensorProof
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof

/-! # An ample diagonal correspondence from the difference map -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

namespace AmpleDiagonal

variable {S : Scheme.{u}} (A : AbelianScheme S)

private abbrev inversion : A.X ⟶ A.X := (𝟙 A.X)⁻¹

private lemma inversion_inversion : inversion A ≫ inversion A = 𝟙 A.X := by
  rw [GrpObj.comp_inv, Category.comp_id, inv_inv]

private instance : IsIso (inversion A).left :=
  ⟨(inversion A).left, congrArg CommaMorphism.left (inversion_inversion A),
    congrArg CommaMorphism.left (inversion_inversion A)⟩

private lemma one_left : (1 : A.X ⟶ A.X).left = A.X.hom ≫ unitSection A := by
  have h : Over.mkIdTerminal.from A.X ≫ (1 : Over.mk (𝟙 S) ⟶ A.X) = 1 := by simp
  simpa only [Over.comp_left, Over.mkIdTerminal_from_left, unitSection] using
    (congrArg CommaMorphism.left h).symm

private abbrev negativeSecond : mumfordProduct A ⟶ A.X := (mumfordSecond A)⁻¹

private abbrev difference : mumfordProduct A ⟶ A.X :=
  mumfordFirst A * negativeSecond A

private def secondAxis : A.X ⟶ mumfordProduct A :=
  Over.homMk (pullback.lift (A.X.hom ≫ unitSection A) (𝟙 A.X.left)
    (by simp [Category.assoc, unitSection_comp])) (by
      change _ ≫ (pullback.fst A.X.hom A.X.hom ≫ A.X.hom) = _
      rw [pullback.lift_fst_assoc]
      simp [Category.assoc, unitSection_comp])

private lemma secondAxis_first : secondAxis A ≫ mumfordFirst A = 1 := by
  apply Over.OverMorphism.ext
  change pullback.lift (A.X.hom ≫ unitSection A) (𝟙 A.X.left) _ ≫
    pullback.fst A.X.hom A.X.hom = (1 : A.X ⟶ A.X).left
  rw [pullback.lift_fst, one_left]

private lemma secondAxis_second : secondAxis A ≫ mumfordSecond A = 𝟙 A.X := by
  apply Over.OverMorphism.ext
  change pullback.lift (A.X.hom ≫ unitSection A) (𝟙 A.X.left) _ ≫
    pullback.snd A.X.hom A.X.hom = 𝟙 A.X.left
  rw [pullback.lift_snd]

private def diagonal : A.X ⟶ mumfordProduct A :=
  Over.homMk (pullback.diagonal A.X.hom) (by
    change _ ≫ (pullback.fst A.X.hom A.X.hom ≫ A.X.hom) = _
    simp [← Category.assoc])

private lemma diagonal_first : diagonal A ≫ mumfordFirst A = 𝟙 A.X := by
  apply Over.OverMorphism.ext
  exact pullback.diagonal_fst A.X.hom

private lemma diagonal_second : diagonal A ≫ mumfordSecond A = 𝟙 A.X := by
  apply Over.OverMorphism.ext
  exact pullback.diagonal_snd A.X.hom

private abbrev tensorIsoOf {X : Scheme.{u}} {M M' N N' : X.Modules}
    (e : M ≅ M') (d : N ≅ N') : tensorObj M N ≅ tensorObj M' N' :=
  (tensorFunctor X).mapIso (e.prod d)

private def pullbackTensorIso {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (tensorObj M N) ≅
      tensorObj ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) := by
  letI := pullbackTensorComparisonIsIso f
  exact (asIso (pullbackTensorComparison f)).app (M, N)

/-- The difference correspondence of `L` and an inverse `M` is an actual line bundle. -/
def correspondence (L M : LineBundle A.X.left) : LineBundle (mumfordProduct A).left :=
  LineBundle.tensor pullbackTensorComparisonIsIso
    (LineBundle.tensor pullbackTensorComparisonIsIso
      ((LineBundle.pullback (difference A).left).obj M)
      ((LineBundle.pullback (mumfordFirst A).left).obj L))
    ((LineBundle.pullback (negativeSecond A).left).obj L)

private def pullbackCompositeIso (t : A.X ⟶ mumfordProduct A)
    (r : mumfordProduct A ⟶ A.X) (f : A.X ⟶ A.X) (w : t ≫ r = f)
    (L : LineBundle A.X.left) :
    (Scheme.Modules.pullback t.left).obj ((Scheme.Modules.pullback r.left).obj L.obj) ≅
      (Scheme.Modules.pullback f.left).obj L.obj :=
  (Scheme.Modules.pullbackComp t.left r.left).app L.obj ≪≫
    (Scheme.Modules.pullbackCongr (congrArg CommaMorphism.left w)).app L.obj

private def restrictionIso (L M : LineBundle A.X.left)
    (t : A.X ⟶ mumfordProduct A) (f g h : A.X ⟶ A.X)
    (wd : t ≫ difference A = f) (w₁ : t ≫ mumfordFirst A = g)
    (w₂ : t ≫ negativeSecond A = h) :
    (Scheme.Modules.pullback t.left).obj (correspondence A L M).obj ≅
      tensorObj (tensorObj ((Scheme.Modules.pullback f.left).obj M.obj)
        ((Scheme.Modules.pullback g.left).obj L.obj))
        ((Scheme.Modules.pullback h.left).obj L.obj) :=
  pullbackTensorIso t.left _ _ ≪≫
    tensorIsoOf
      (pullbackTensorIso t.left _ _ ≪≫
        tensorIsoOf (pullbackCompositeIso A t _ f wd M)
          (pullbackCompositeIso A t _ g w₁ L))
      (pullbackCompositeIso A t _ h w₂ L)

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

private def constantIso (L : LineBundle A.X.left) :
    (Scheme.Modules.pullback (1 : A.X ⟶ A.X).left).obj L.obj ≅
      structureSheaf A.X.left :=
  (Scheme.Modules.pullbackCongr (one_left A)).app L.obj ≪≫
    ((Scheme.Modules.pullbackComp A.X.hom (unitSection A)).app L.obj).symm ≪≫
    (Scheme.Modules.pullback A.X.hom).mapIso
      (fieldLineBundleTriviality K ((LineBundle.pullback (unitSection A)).obj L)).some ≪≫
    pullbackUnitIso A.X.hom

variable (L M : LineBundle A.X.left)
    (evaluation : tensorObj L.obj M.obj ≅ structureSheaf A.X.left)

/-- The first unit axis of the difference correspondence is actually trivial. -/
def firstAxisIso :
    (Scheme.Modules.pullback (mumfordSection A)).obj (correspondence A L M).obj ≅
      structureSheaf A.X.left :=
  restrictionIso A L M (mumfordSectionOver A) (𝟙 A.X) (𝟙 A.X) 1
    (by simp [difference, negativeSecond, MonObj.comp_mul, GrpObj.comp_inv])
    (mumfordSectionOver_first A)
    (by simp [negativeSecond, GrpObj.comp_inv]) ≪≫
  tensorIsoOf
    (tensorIsoOf ((Scheme.Modules.pullbackId A.X.left).app M.obj)
        ((Scheme.Modules.pullbackId A.X.left).app L.obj) ≪≫
      tensorComm M.obj L.obj ≪≫ evaluation)
    (constantIso A L) ≪≫
  tensorLeftUnitor _

/-- The second unit axis of the difference correspondence is actually trivial. -/
def secondAxisIso :
    (Scheme.Modules.pullback
      (pullback.lift (A.X.hom ≫ unitSection A) (𝟙 A.X.left)
        (by simp [Category.assoc, unitSection_comp]))).obj (correspondence A L M).obj ≅
      structureSheaf A.X.left :=
  restrictionIso A L M (secondAxis A) (inversion A) 1 (inversion A)
    (by simp [difference, negativeSecond, MonObj.comp_mul, GrpObj.comp_inv,
      secondAxis_first, secondAxis_second])
    (secondAxis_first A)
    (by simp [negativeSecond, GrpObj.comp_inv, secondAxis_second]) ≪≫
  tensorIsoOf (tensorIsoOf (Iso.refl _) (constantIso A L) ≪≫ tensorRightUnitor _)
    (Iso.refl _) ≪≫
  (pullbackTensorIso (inversion A).left M.obj L.obj).symm ≪≫
  (Scheme.Modules.pullback (inversion A).left).mapIso
    (tensorComm M.obj L.obj ≪≫ evaluation) ≪≫
  pullbackUnitIso (inversion A).left

/-- On the diagonal the difference correspondence is `L tensor [-1]*L`. -/
def diagonalIso :
    (Scheme.Modules.pullback (pullback.diagonal A.X.hom)).obj (correspondence A L M).obj ≅
      tensorObj L.obj ((Scheme.Modules.pullback (inversion A).left).obj L.obj) :=
  restrictionIso A L M (diagonal A) 1 (𝟙 A.X) (inversion A)
    (by simp [difference, negativeSecond, MonObj.comp_mul, GrpObj.comp_inv,
      diagonal_first, diagonal_second])
    (diagonal_first A)
    (by simp [negativeSecond, GrpObj.comp_inv, diagonal_second]) ≪≫
  tensorIsoOf
    (tensorIsoOf (constantIso A M) ((Scheme.Modules.pullbackId A.X.left).app L.obj) ≪≫
      tensorLeftUnitor L.obj)
    (Iso.refl _)

set_option maxHeartbeats 800000 in
/-- An ample bundle gives an ample diagonal pullback, using only actual operations. -/
theorem diagonal_isAmple (hL : L.IsAmple) :
    ((LineBundle.pullback (pullback.diagonal A.X.hom)).obj
      (correspondence A L M)).IsAmple := by
  have hi : ((LineBundle.pullback (inversion A).left).obj L).IsAmple :=
    closedImmersionPullbackAmple _ _ (inversion A).left L inferInstance hL
  exact ampleTensor A.X.left L ((LineBundle.pullback (inversion A).left).obj L)
    ((LineBundle.pullback (pullback.diagonal A.X.hom)).obj (correspondence A L M))
    ⟨(diagonalIso A L M).symm⟩ hL hi

end AmpleDiagonal

/-- Every ample bundle over a field supplies a correspondence trivial on both axes
whose actual diagonal pullback is ample. -/
theorem fieldAmpleDiagonalCorrespondence : FieldAmpleDiagonalCorrespondenceStatement.{u} := by
  intro K _ A ⟨L, hL⟩
  obtain ⟨M, ⟨evaluation⟩⟩ := L.exists_tensorObj_iso_structureSheaf
  exact ⟨AmpleDiagonal.correspondence A L M,
    ⟨AmpleDiagonal.firstAxisIso A L M evaluation⟩,
    ⟨AmpleDiagonal.secondAxisIso A L M evaluation⟩,
    AmpleDiagonal.diagonal_isAmple A L M hL⟩

end Langlands.AbelianScheme
