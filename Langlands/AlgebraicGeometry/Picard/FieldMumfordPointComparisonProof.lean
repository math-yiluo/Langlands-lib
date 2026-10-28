import Langlands.AlgebraicGeometry.Picard.FieldMumfordPointComparisonStatement
import Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroReduction
import Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedCarrierIso
import Langlands.AlgebraicGeometry.Picard.TranslationBaseChange

/-! # Proof of the rigidified Mumford comparison at field-valued points

The theorem `fieldMumfordPointComparison` proves `FieldMumfordPointComparisonStatement`.
Pulling the three Mumford factors back along `a × id : Spec K ×_k A → A ×_k A` turns
addition into translation by `x`, the parameter projection into a map through `Spec K`
and the second projection into the projection to `A`. With the triviality of line
bundles on `Spec K` and the premise this gives an isomorphism of underlying modules,
which `RigidifiedLineBundle.isoOfCarrierIso` corrects to a rigidified isomorphism. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme.FieldMumfordPoint

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AbelianScheme.MumfordPicardZero (pullbackTensorIso pullbackCompIso tensorIsoOf)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S S' : Scheme.{u}} (A : AbelianScheme S) {b : S' ⟶ S} (a : Over.mk b ⟶ A.X)

/-- The map `a × id : S' ×_S A → A ×_S A` underlying the relative pullback along `a`. -/
abbrev pointMap : pullback b A.X.hom ⟶ pullback A.X.hom A.X.hom :=
  (relativeSpace A.X.hom).map a

/-- The parameter coordinate of `a × id` is `a` on the first factor. -/
lemma pointMap_fst :
    pointMap A a ≫ pullback.fst A.X.hom A.X.hom = pullback.fst b A.X.hom ≫ a.left := by
  simp [pointMap, relativeSpace]

/-- The second coordinate of `a × id` is the projection to `A`. -/
lemma pointMap_snd :
    pointMap A a ≫ pullback.snd A.X.hom A.X.hom = pullback.snd b A.X.hom := by
  simp [pointMap, relativeSpace]

/-- Along `a × id`, addition becomes translation by the lift `x` of `a` on the base
change, read through the symmetry `S' ×_S A ≅ A ×_S S'`. -/
lemma pointMap_addition
    (x : Over.mk (𝟙 S') ⟶ ((baseChange b).obj A).X)
    (hx : x.left ≫ pullback.fst A.X.hom b = a.left) :
    pointMap A a ≫ mumfordAddition A =
      (pullbackSymmetry b A.X.hom).hom ≫
        (GroupScheme.translation ((baseChange b).obj A).toGrp x).left ≫
          pullback.fst A.X.hom b := by
  let W : Over S := Over.mk (pullback.fst b A.X.hom ≫ b)
  let φ : W ⟶ mumfordProduct A := Over.homMk (pointMap A a) (by
    change pointMap A a ≫ pullback.fst A.X.hom A.X.hom ≫ A.X.hom = _
    rw [← Category.assoc, pointMap_fst, Category.assoc, Over.w a]
    rfl)
  let σ : W ⟶ (Over.map b).obj ((baseChange b).obj A).X :=
    Over.homMk (pullbackSymmetry b A.X.hom).hom (by
      change (pullbackSymmetry b A.X.hom).hom ≫ pullback.snd A.X.hom b ≫ b = _
      rw [pullbackSymmetry_hom_comp_snd_assoc]
      rfl)
  let G := (GroupScheme.baseChange b).obj A.toGrp
  let x' : Over.mk (𝟙 S') ⟶ G.X := x
  let Φ := GroupScheme.baseChangePointsEquiv b A.toGrp G.X
  have h := GroupScheme.baseChangePointsEquiv_translation b A.toGrp x'
  have key : φ ≫ (mumfordFirst A * mumfordSecond A) =
      σ ≫ Φ (GroupScheme.translation G x') := by
    rw [h, MonObj.comp_mul, MonObj.comp_mul]
    congr 1
    · apply Over.OverMorphism.ext
      simp only [Over.comp_left, φ, σ, mumfordFirst, Over.homMk_left, Over.map_map_left,
        GroupScheme.baseChangePointsEquiv_left, Over.mkIdTerminal_from_left]
      rw [pointMap_fst, ← hx]
      exact (pullbackSymmetry_hom_comp_snd_assoc _ _ _).symm
    · apply Over.OverMorphism.ext
      simp only [Over.comp_left, φ, σ, mumfordSecond, Over.homMk_left,
        GroupScheme.baseChangePointsEquiv_left]
      rw [pointMap_snd, Over.id_left, Category.id_comp, pullbackSymmetry_hom_comp_fst]
  have key' := congrArg CommaMorphism.left key
  simp only [Over.comp_left, φ, σ, Φ, GroupScheme.baseChangePointsEquiv_left] at key'
  exact key'

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})

/-- The comparison of underlying modules: pulling the three Mumford factors back
along `a × id` gives `t_x^*(i^*L₀) ⊗ i^*M₀` (read through the symmetry), up to the
factor pulled back from `S'`, which `triv` trivializes; `premise` identifies the
result with `Qc`. -/
def carrierIso
    (x : Over.mk (𝟙 S') ⟶ ((baseChange b).obj A).X)
    (hx : x.left ≫ pullback.fst A.X.hom b = a.left)
    (L₀ M₀ : A.X.left.Modules) (Qc : (pullback b A.X.hom).Modules)
    (triv : (Scheme.Modules.pullback a.left).obj M₀ ≅ structureSheaf S')
    (premise : tensorObj
        ((Scheme.Modules.pullback
          (GroupScheme.translation ((baseChange b).obj A).toGrp x).left).obj
            ((Scheme.Modules.pullback (pullback.fst A.X.hom b)).obj L₀))
        ((Scheme.Modules.pullback (pullback.fst A.X.hom b)).obj M₀) ≅
      (Scheme.Modules.pullback (pullbackSymmetry b A.X.hom).inv).obj Qc) :
    (Scheme.Modules.pullback (pointMap A a)).obj
        (tensorObj (tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj L₀)
          ((Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj M₀))
          ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj M₀)) ≅ Qc :=
  let σ := pullbackSymmetry b A.X.hom
  let t := (GroupScheme.translation ((baseChange b).obj A).toGrp x).left
  let i := pullback.fst A.X.hom b
  pullbackTensorIso preservation (pointMap A a) _ _ ≪≫
    tensorIsoOf
      (pullbackTensorIso preservation (pointMap A a) _ _ ≪≫
        tensorIsoOf
          ((Scheme.Modules.pullbackComp (pointMap A a) (mumfordAddition A)).app L₀ ≪≫
            pullbackCompIso σ.hom (t ≫ i) _ (pointMap_addition A a x hx).symm L₀ ≪≫
            (Scheme.Modules.pullback σ.hom).mapIso (pullbackCompIso t i _ rfl L₀))
          ((Scheme.Modules.pullbackComp (pointMap A a)
              (pullback.fst A.X.hom A.X.hom)).app M₀ ≪≫
            pullbackCompIso (pullback.fst b A.X.hom) a.left _ (pointMap_fst A a).symm M₀ ≪≫
            (Scheme.Modules.pullback (pullback.fst b A.X.hom)).mapIso triv ≪≫
            pullbackUnitIso (pullback.fst b A.X.hom)) ≪≫
        tensorRightUnitor _)
      ((Scheme.Modules.pullbackComp (pointMap A a) (pullback.snd A.X.hom A.X.hom)).app M₀ ≪≫
        pullbackCompIso σ.hom i _
          ((pullbackSymmetry_hom_comp_fst _ _).trans (pointMap_snd A a).symm) M₀) ≪≫
    (pullbackTensorIso preservation σ.hom _ _).symm ≪≫
    (Scheme.Modules.pullback σ.hom).mapIso premise ≪≫
    (Scheme.Modules.pullbackComp σ.hom σ.inv).app Qc ≪≫
    (Scheme.Modules.pullbackCongr σ.hom_inv_id).app Qc ≪≫
    (Scheme.Modules.pullbackId _).app Qc

end Langlands.AbelianScheme.FieldMumfordPoint

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The rigidified Mumford comparison at field-valued points. -/
theorem fieldMumfordPointComparison : FieldMumfordPointComparisonStatement.{u} := by
  intro preservation k _ A L M evaluation K _ b a x hx Q ⟨premise⟩
  exact ⟨RigidifiedLineBundle.isoOfCarrierIso preservation
    ((relativeProjection A.X.hom).app (Over.mk b))
    (relativeSection_projection _ _ _ _)
    (FieldMumfordPoint.carrierIso A a preservation x hx L.obj.carrier M.obj Q.obj.carrier
      (fieldLineBundleTriviality K ((LineBundle.pullback a.left).obj M)).some
      ((LineBundle.forget _).mapIso premise))⟩

end Langlands.AbelianScheme
