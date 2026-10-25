import Langlands.AlgebraicGeometry.Picard.MumfordSchemeMapHomomorphismStatement
import Langlands.AlgebraicGeometry.Picard.RigidificationAdjustment

/-! # The unit equation for the actual Mumford map -/

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {S : Scheme.{u}} (A : AbelianScheme S)

lemma unitPoint_left (T : Over S) :
    (1 : T ⟶ A.X).left = T.hom ≫ unitSection A := by
  have h : Over.mkIdTerminal.from T ≫ (1 : Over.mk (𝟙 S) ⟶ A.X) = 1 := by simp
  simpa only [Over.comp_left, Over.mkIdTerminal_from_left, unitSection] using
    (congrArg (fun f : T ⟶ A.X => f.left) h).symm

lemma mumfordZeroParameter_addition (T : Over S) :
    (relativeSpace A.X.hom).map (1 : T ⟶ A.X) ≫ mumfordAddition A =
      pullback.snd T.hom A.X.hom := by
  let D : Over S := Over.mk (pullback.snd T.hom A.X.hom ≫ A.X.hom)
  let h : D ⟶ mumfordProduct A := Over.homMk
    ((relativeSpace A.X.hom).map (1 : T ⟶ A.X)) (by
      change _ ≫ (pullback.fst A.X.hom A.X.hom ≫ A.X.hom) = _
      simp only [relativeSpace, Functor.comp_map, Over.forget_map, Over.pullback_map_left,
        pullback.lift_fst_assoc, Category.assoc, Over.w]
      exact pullback.condition (f := T.hom) (g := A.X.hom))
  let q : D ⟶ A.X := Over.homMk (pullback.snd T.hom A.X.hom)
  have hf : h ≫ mumfordFirst A = 1 := by
    apply Over.OverMorphism.ext
    change (relativeSpace A.X.hom).map (1 : T ⟶ A.X) ≫
      pullback.fst A.X.hom A.X.hom = (1 : D ⟶ A.X).left
    simp only [relativeSpace, Functor.comp_map, Over.forget_map, Over.pullback_map_left,
      pullback.lift_fst, unitPoint_left]
    simpa [D, Category.assoc] using congrArg (fun k => k ≫ unitSection A)
      (pullback.condition (f := T.hom) (g := A.X.hom))
  have hs : h ≫ mumfordSecond A = q := by
    apply Over.OverMorphism.ext
    exact pullback.lift_snd _ _ _
  change (h ≫ (mumfordFirst A * mumfordSecond A)).left = q.left
  rw [MonObj.comp_mul, hf, hs, one_mul]

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (L : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
variable (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left)

/-- The ordinary module underlying the zero-parameter pullback is trivial. -/
def mumfordZeroParameterCarrierIso (T : Over S) :
    ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
      (unitSection_comp A) (1 : T ⟶ A.X)).obj
        (mumfordBundle A preservation L M evaluation)).obj.carrier ≅
      structureSheaf ((relativeSpace A.X.hom).obj T) := by
  let h := (relativeSpace A.X.hom).map (1 : T ⟶ A.X)
  let p := pullback.fst T.hom A.X.hom ≫ T.hom
  let q := pullback.snd T.hom A.X.hom
  letI := preservation h
  letI := preservation q
  have hf : h ≫ pullback.fst A.X.hom A.X.hom = p ≫ unitSection A := by
    simp [h, p, relativeSpace, Over.pullback, unitPoint_left, Category.assoc, pullback.lift_fst]
  let eL : (Scheme.Modules.pullback h).obj
      ((Scheme.Modules.pullback (mumfordAddition A)).obj L.obj.carrier) ≅
      (Scheme.Modules.pullback q).obj L.obj.carrier :=
    (Scheme.Modules.pullbackComp h (mumfordAddition A)).app L.obj.carrier ≪≫
      (Scheme.Modules.pullbackCongr (mumfordZeroParameter_addition A T)).app L.obj.carrier
  let eM : (Scheme.Modules.pullback h).obj
      ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj M.obj) ≅
      (Scheme.Modules.pullback q).obj M.obj :=
    (Scheme.Modules.pullbackComp h (pullback.snd A.X.hom A.X.hom)).app M.obj ≪≫
      (Scheme.Modules.pullbackCongr (by
        simp [h, q, relativeSpace, Over.pullback, pullback.lift_snd])).app M.obj
  let e0 : (Scheme.Modules.pullback h).obj
      ((Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj M.obj) ≅
      structureSheaf ((relativeSpace A.X.hom).obj T) :=
    (Scheme.Modules.pullbackComp h (pullback.fst A.X.hom A.X.hom)).app M.obj ≪≫
      (Scheme.Modules.pullbackCongr hf).app M.obj ≪≫
      ((Scheme.Modules.pullbackComp p (unitSection A)).app M.obj).symm ≪≫
      (Scheme.Modules.pullback p).mapIso
        (Langlands.SchemeModule.RigidifiedModule.inverseTrivialization
          preservation L.obj M.obj evaluation) ≪≫ pullbackUnitIso p
  let c1 := (asIso (pullbackTensorComparison h)).app
    ((Scheme.Modules.pullback (mumfordAddition A)).obj L.obj.carrier,
     (Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj M.obj)
  let c2 := (asIso (pullbackTensorComparison h)).app
    (tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj L.obj.carrier)
      ((Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj M.obj),
     (Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj M.obj)
  exact c2 ≪≫ (tensorFunctor _).mapIso
    ((c1 ≪≫ (tensorFunctor _).mapIso (eL.prod e0) ≪≫
      tensorRightUnitor ((Scheme.Modules.pullback q).obj L.obj.carrier)).prod eM) ≪≫
    ((asIso (pullbackTensorComparison q)).app (L.obj.carrier, M.obj)).symm ≪≫
    (Scheme.Modules.pullback q).mapIso evaluation ≪≫ pullbackUnitIso q

/-- The trivialization can be chosen to respect the actual rigidification. -/
def mumfordZeroParameterIso (T : Over S) :
    (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
      (unitSection_comp A) (1 : T ⟶ A.X)).obj
        (mumfordBundle A preservation L M evaluation) ≅
      RigidifiedLineBundle.trivial
        ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T) :=
  RigidifiedLineBundle.trivialIsoOfCarrierIso
    (pullback.fst T.hom A.X.hom) _
    (relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) T) _
    (mumfordZeroParameterCarrierIso A preservation L M evaluation T)

variable (stability : PicardZeroPullbackStatement.{u})
variable (square : MumfordBundlePicardZeroStatement.{u}) (hA : HasDualScheme A)

include stability in
/-- The constructed map takes the zero point on every test scheme to the dual origin. -/
lemma mumfordSchemeMap_zero (T : Over S) :
    (1 : T ⟶ A.X) ≫ mumfordSchemeMap preservation square A L M evaluation hA =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA := by
  apply dualPointClass_injective stability A hA T
  rw [dualPointClass_origin]
  apply Subtype.ext
  change RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
    (poincareFamily A hA) T
    ((1 : T ⟶ A.X) ≫ mumfordSchemeMap preservation square A L M evaluation hA) = _
  rw [mumfordSchemeMap_points]
  exact Quotient.sound ⟨mumfordZeroParameterIso A preservation L M evaluation T⟩

include stability in
/-- The unit equation in the original homomorphism target, over every base scheme. -/
lemma mumfordSchemeMap_unit :
    η[A.X] ≫ mumfordSchemeMap preservation square A L M evaluation hA =
      (Over.homMk (MonoidalCategory.tensorUnit (Over S)).hom :
        MonoidalCategory.tensorUnit (Over S) ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA := by
  rw [MonObj.one_eq_one]
  exact mumfordSchemeMap_zero A preservation L M evaluation stability square hA _

end Langlands.AbelianScheme
