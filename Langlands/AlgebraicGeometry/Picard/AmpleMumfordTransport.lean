import Langlands.AlgebraicGeometry.Picard.AmpleMumfordBaseChange
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoLemmas
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedCarrierIso

/-! # Ample Mumford presentations along homomorphisms of abelian schemes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {T : Scheme.{u}} {X Y : AbelianScheme T} (g : Y ⟶ X)

/-- A homomorphism commutes with the structure morphisms. -/
@[reassoc (attr := simp)]
lemma hom_comp_structure : hom g ≫ X.X.hom = Y.X.hom :=
  Over.w (groupHom g).hom.hom

/-- A homomorphism carries the unit section to the unit section. -/
@[reassoc (attr := simp)]
lemma unitSection_comp_hom : unitSection Y ≫ hom g = unitSection X := by
  change ((1 : Over.mk (𝟙 T) ⟶ Y.X) ≫ (groupHom g).hom.hom).left = _
  rw [MonObj.one_comp]
  rfl

/-- The map of parameter-first self-products induced by a homomorphism. -/
def mumfordProductMap : (mumfordProduct Y).left ⟶ (mumfordProduct X).left :=
  pullback.map Y.X.hom Y.X.hom X.X.hom X.X.hom (hom g) (hom g) (𝟙 T)
    (by simp) (by simp)

@[reassoc (attr := simp)]
lemma mumfordProductMap_fst :
    mumfordProductMap g ≫ pullback.fst X.X.hom X.X.hom =
      pullback.fst Y.X.hom Y.X.hom ≫ hom g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma mumfordProductMap_snd :
    mumfordProductMap g ≫ pullback.snd X.X.hom X.X.hom =
      pullback.snd Y.X.hom Y.X.hom ≫ hom g :=
  pullback.lift_snd _ _ _

/-- The same map of self-products as a morphism over the base. -/
def mumfordProductMapOver : mumfordProduct Y ⟶ mumfordProduct X :=
  Over.homMk (mumfordProductMap g) (by
    change mumfordProductMap g ≫ pullback.fst X.X.hom X.X.hom ≫ X.X.hom =
      pullback.fst Y.X.hom Y.X.hom ≫ Y.X.hom
    rw [mumfordProductMap_fst_assoc, hom_comp_structure])

/-- The induced map of self-products is compatible with addition. -/
lemma mumfordProductMap_addition :
    mumfordProductMap g ≫ mumfordAddition X = mumfordAddition Y ≫ hom g := by
  have h1 : mumfordProductMapOver g ≫ mumfordFirst X =
      mumfordFirst Y ≫ (groupHom g).hom.hom := by
    apply Over.OverMorphism.ext
    exact mumfordProductMap_fst g
  have h2 : mumfordProductMapOver g ≫ mumfordSecond X =
      mumfordSecond Y ≫ (groupHom g).hom.hom := by
    apply Over.OverMorphism.ext
    exact mumfordProductMap_snd g
  have h : mumfordProductMapOver g ≫ (mumfordFirst X * mumfordSecond X) =
      (mumfordFirst Y * mumfordSecond Y) ≫ (groupHom g).hom.hom := by
    rw [MonObj.comp_mul, MonObj.mul_comp, h1, h2]
  exact congrArg (fun k ↦ k.left) h

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})

/-- Pull back the bundle `L ⊗ π^* B` underlying a normalization along a homomorphism. -/
def normalizedBundlePullbackIso (L : LineBundle X.X.left) (B : LineBundle T) :
    (LineBundle.pullback (hom g)).obj
        (LineBundle.tensor preservation L ((LineBundle.pullback X.X.hom).obj B)) ≅
      LineBundle.tensor preservation ((LineBundle.pullback (hom g)).obj L)
        ((LineBundle.pullback Y.X.hom).obj B) :=
  LineBundle.pullbackTensorObjIso preservation (hom g) L _ ≪≫
    LineBundle.tensorIso preservation (Iso.refl _)
      (LineBundle.pullbackCompEqIso (hom g) X.X.hom (hom_comp_structure g) B)

/-- The unit-section evaluation transported to the pulled-back bundle. -/
def pullbackUnitEvaluation (L : LineBundle X.X.left) (B : LineBundle T)
    (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection X)).obj L.obj) B.obj ≅
      structureSheaf T) :
    tensorObj ((Scheme.Modules.pullback (unitSection Y)).obj
        ((LineBundle.pullback (hom g)).obj L).obj) B.obj ≅ structureSheaf T :=
  (Langlands.Scheme.Modules.tensorFunctor T).mapIso
      (((Scheme.Modules.pullbackComp (unitSection Y) (hom g)).app L.obj ≪≫
        (Scheme.Modules.pullbackCongr (unitSection_comp_hom g)).app L.obj).prod
          (Iso.refl B.obj)) ≪≫
    evaluationB

/-- The inverse evaluation of a normalized bundle transported along a homomorphism. -/
def pullbackNormalizedEvaluation (L : LineBundle X.X.left) (B : LineBundle T)
    (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection X)).obj L.obj) B.obj ≅
      structureSheaf T)
    (M : LineBundle X.X.left)
    (evaluation : tensorObj
      (LineBundle.normalize preservation X.X.hom (unitSection X) (unitSection_comp X)
        L B evaluationB).obj.carrier M.obj ≅ structureSheaf X.X.left)
    (evaluationB' : tensorObj ((Scheme.Modules.pullback (unitSection Y)).obj
        ((LineBundle.pullback (hom g)).obj L).obj) B.obj ≅ structureSheaf T) :
    tensorObj
      (LineBundle.normalize preservation Y.X.hom (unitSection Y) (unitSection_comp Y)
        ((LineBundle.pullback (hom g)).obj L) B evaluationB').obj.carrier
        ((LineBundle.pullback (hom g)).obj M).obj ≅ structureSheaf Y.X.left := by
  letI := preservation (hom g)
  exact (Langlands.Scheme.Modules.tensorFunctor Y.X.left).mapIso
      (((LineBundle.forget _).mapIso (normalizedBundlePullbackIso g preservation L B)).symm.prod
        (Iso.refl _)) ≪≫
    ((asIso (pullbackTensorComparison (hom g))).app
      ((LineBundle.tensor preservation L ((LineBundle.pullback X.X.hom).obj B)).obj,
        M.obj)).symm ≪≫
    (Scheme.Modules.pullback (hom g)).mapIso evaluation ≪≫
    pullbackUnitIso (hom g)

/-- Pullback of the ordinary bundle `m^*(L ⊗ π^*B) ⊗ p₁^*M ⊗ p₂^*M` underlying a
normalized Mumford family along the induced map of self-products. -/
def mumfordBundlePullbackIso (L : LineBundle X.X.left) (B : LineBundle T)
    (M : LineBundle X.X.left) :
    (LineBundle.pullback (mumfordProductMap g)).obj
        (LineBundle.tensor preservation
          (LineBundle.tensor preservation
            ((LineBundle.pullback (mumfordAddition X)).obj
              (LineBundle.tensor preservation L ((LineBundle.pullback X.X.hom).obj B)))
            ((LineBundle.pullback (pullback.fst X.X.hom X.X.hom)).obj M))
          ((LineBundle.pullback (pullback.snd X.X.hom X.X.hom)).obj M)) ≅
      LineBundle.tensor preservation
        (LineBundle.tensor preservation
          ((LineBundle.pullback (mumfordAddition Y)).obj
            (LineBundle.tensor preservation ((LineBundle.pullback (hom g)).obj L)
              ((LineBundle.pullback Y.X.hom).obj B)))
          ((LineBundle.pullback (pullback.fst Y.X.hom Y.X.hom)).obj
            ((LineBundle.pullback (hom g)).obj M)))
        ((LineBundle.pullback (pullback.snd Y.X.hom Y.X.hom)).obj
          ((LineBundle.pullback (hom g)).obj M)) :=
  LineBundle.pullbackTensorObjIso preservation _ _ _ ≪≫
    LineBundle.tensorIso preservation
      (LineBundle.pullbackTensorObjIso preservation _ _ _ ≪≫
        LineBundle.tensorIso preservation
          (LineBundle.pullbackCompEqIso _ _ (mumfordProductMap_addition g) _ ≪≫
            (LineBundle.pullbackCompEqIso _ _ rfl _).symm ≪≫
            (LineBundle.pullback (mumfordAddition Y)).mapIso
              (normalizedBundlePullbackIso g preservation L B))
          (LineBundle.pullbackCompEqIso _ _ (mumfordProductMap_fst g) _ ≪≫
            (LineBundle.pullbackCompEqIso _ _ rfl _).symm))
      (LineBundle.pullbackCompEqIso _ _ (mumfordProductMap_snd g) _ ≪≫
        (LineBundle.pullbackCompEqIso _ _ rfl _).symm)

variable (square : MumfordBundlePicardZeroStatement.{u})

/-- An ample Mumford presentation pulls back along a homomorphism of abelian schemes
whose underlying morphism is a closed immersion, provided the two classifying maps have
compatible Poincare pullbacks after forgetting rigidifications. -/
theorem hasAmpleMumfordPresentation_of_homomorphism [IsClosedImmersion (hom g)]
    (hX : HasDualScheme X) (hY : HasDualScheme Y)
    (fX : X.X ⟶ dualScheme X hX) (fY : Y.X ⟶ dualScheme Y hY)
    (compat : Nonempty
      ((RigidifiedLineBundle.forget (mumfordSection Y)).obj
          ((RigidifiedLineBundle.relativePullback Y.X.hom (unitSection Y) (unitSection_comp Y)
            fY).obj (poincareFamily Y hY)) ≅
        (LineBundle.pullback (mumfordProductMap g)).obj
          ((RigidifiedLineBundle.forget (mumfordSection X)).obj
            ((RigidifiedLineBundle.relativePullback X.X.hom (unitSection X)
              (unitSection_comp X) fX).obj (poincareFamily X hX)))))
    (h : HasAmpleMumfordPresentation preservation square X hX fX) :
    HasAmpleMumfordPresentation preservation square Y hY fY := by
  obtain ⟨e⟩ := compat
  obtain ⟨L, B, evaluationB, M, evaluation, hL, rfl⟩ := h
  let evaluationB' := pullbackUnitEvaluation g L B evaluationB
  let evaluation' :=
    pullbackNormalizedEvaluation g preservation L B evaluationB M evaluation evaluationB'
  refine ⟨(LineBundle.pullback (hom g)).obj L, B, evaluationB',
    (LineBundle.pullback (hom g)).obj M, evaluation',
    closedImmersionPullbackAmple _ _ (hom g) L inferInstance hL, ?_⟩
  rw [eq_mumfordSchemeMapOfLineBundle_iff]
  exact RigidifiedLineBundle.nonempty_iso_of_forget_iso preservation
    ((relativeProjection Y.X.hom).app Y.X)
    (relativeSection_projection Y.X.hom (unitSection Y) (unitSection_comp Y) Y.X)
    (e ≪≫ (LineBundle.pullback (mumfordProductMap g)).mapIso
      ((RigidifiedLineBundle.forget _).mapIso
        (mumfordSchemeMapOfLineBundlePullbackIso preservation X L B evaluationB M evaluation
          square hX) ≪≫
        eqToIso (mumfordFamilyOfLineBundle_forget preservation X L B evaluationB M
          evaluation)) ≪≫
      mumfordBundlePullbackIso g preservation L B M ≪≫
      eqToIso (mumfordFamilyOfLineBundle_forget preservation Y _ B evaluationB' _
        evaluation').symm)

end Langlands.AbelianScheme
