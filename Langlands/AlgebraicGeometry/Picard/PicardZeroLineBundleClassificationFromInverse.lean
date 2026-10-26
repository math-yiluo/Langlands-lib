import Langlands.AlgebraicGeometry.Picard.PicardZeroLineBundleClassificationStatement
import Langlands.AlgebraicGeometry.Picard.LineBundleNormalization
import Langlands.AlgebraicGeometry.Picard.GeometricPicardZeroTensor
import Langlands.AlgebraicGeometry.Modules.TensorCoherenceMaps

/-! # Classification of Picard-zero line bundles from supplied tensor inverses -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- A line bundle pulled back along the structure map is translation invariant. -/
lemma isTranslationInvariant_pullback_structure (M : LineBundle S) :
    IsTranslationInvariant G ((LineBundle.pullback G.X.hom).obj M) := by
  intro x
  exact ⟨(LineBundle.pullbackComp (translation G x).left G.X.hom).app M ≪≫
    eqToIso (by rw [Over.w (translation G x)])⟩

end Langlands.GroupScheme

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {S : Scheme.{u}}

/-- A line bundle pulled back along the structure map is Picard-zero on geometric fibres. -/
lemma isGeometricallyPicardZero_pullback_structure (B : AbelianScheme S) (M : LineBundle S) :
    IsGeometricallyPicardZero B ((LineBundle.pullback B.X.hom).obj M) := by
  intro K _ _ s
  refine GroupScheme.isTranslationInvariant_of_iso _ ?_
    (GroupScheme.isTranslationInvariant_pullback_structure ((baseChange s).obj B).toGrp
      ((LineBundle.pullback s).obj M))
  exact (LineBundle.pullbackComp (pullback.snd B.X.hom s) s).app M ≪≫
    eqToIso (congrArg (fun g ↦ (LineBundle.pullback g).obj M) pullback.condition.symm) ≪≫
      ((LineBundle.pullbackComp (pullback.fst B.X.hom s) B.X.hom).app M).symm

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})

include preservation in
/-- Tensoring with a line bundle pulled back from the parameter scheme preserves the
geometric Picard-zero condition on `T ×_S A`. -/
lemma isGeometricallyPicardZero_tensor_parameterPullback (A : AbelianScheme S) (T : Over S)
    (N : LineBundle ((relativeSpace A.X.hom).obj T)) (M : LineBundle T.left)
    (hN : IsGeometricallyPicardZero ((baseChange T.hom).obj A)
      ((LineBundle.pullback (relativeSpaceSymmetry A.X.hom T).inv).obj N)) :
    IsGeometricallyPicardZero ((baseChange T.hom).obj A)
      ((LineBundle.pullback (relativeSpaceSymmetry A.X.hom T).inv).obj
        (LineBundle.tensor preservation N
          ((LineBundle.pullback ((relativeProjection A.X.hom).app T)).obj M))) := by
  have h : (relativeSpaceSymmetry A.X.hom T).inv ≫ (relativeProjection A.X.hom).app T =
      ((baseChange T.hom).obj A).X.hom :=
    pullbackSymmetry_inv_comp_fst T.hom A.X.hom
  refine isGeometricallyPicardZero_of_iso _
    (LineBundle.pullbackTensorObjIso preservation (relativeSpaceSymmetry A.X.hom T).inv _ _).symm
    (isGeometricallyPicardZero_tensor preservation _ hN ?_)
  exact isGeometricallyPicardZero_of_iso _
    (eqToIso (congrArg (fun g ↦ (LineBundle.pullback g).obj M) h.symm) ≪≫
      ((LineBundle.pullbackComp (relativeSpaceSymmetry A.X.hom T).inv
        ((relativeProjection A.X.hom).app T)).app M).symm)
    (isGeometricallyPicardZero_pullback_structure ((baseChange T.hom).obj A) M)

/-- Supplied tensor inverses of line bundles give the classification of geometrically
Picard-zero line bundles on `T ×_S A` up to a twist from `T`. -/
theorem picardZeroLineBundleClassification_of_inverse
    (inverse : ∀ {X : Scheme.{u}} (L : LineBundle X), ∃ M : LineBundle X,
      Nonempty (tensorObj L.obj M.obj ≅ structureSheaf X)) :
    PicardZeroLineBundleClassificationStatement.{u} := by
  intro preservation S A hA T N hN
  let f := (relativeProjection A.X.hom).app T
  let ε := (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T
  have section_eq : ε ≫ f = 𝟙 T.left :=
    relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) T
  obtain ⟨M, ⟨evaluation⟩⟩ := inverse ((LineBundle.pullback ε).obj N)
  let L : RigidifiedFamily A T :=
    LineBundle.normalize preservation f ε section_eq N M evaluation
  have hL : IsPicardZeroFamily A L :=
    isGeometricallyPicardZero_tensor_parameterPullback preservation A T N M hN
  refine ⟨dualClassify A hA T
    ⟨RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) L, hL⟩, ⟨?_⟩⟩
  let eP := (LineBundle.forget _).mapIso
    ((RigidifiedLineBundle.forget _).mapIso (dualClassifyPullbackIso A hA L hL))
  letI := preservation f
  refine ObjectProperty.isoMk _ ?_
  exact (tensorRightUnitor N.obj).symm ≪≫
    (tensorFunctor _).mapIso ((Iso.refl N.obj).prod
      ((pullbackUnitIso f).symm ≪≫
        (Scheme.Modules.pullback f).mapIso (evaluation.symm ≪≫ tensorComm _ _) ≪≫
          (asIso (pullbackTensorComparison f)).app
            (M.obj, (Scheme.Modules.pullback ε).obj N.obj))) ≪≫
    (tensorAssociator _ _ _).symm ≪≫
    (tensorFunctor _).mapIso (eP.symm.prod (Iso.refl _))

end Langlands.AbelianScheme
