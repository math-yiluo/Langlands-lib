import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleTranslationStabilizerFiniteStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedProof
import Langlands.AlgebraicGeometry.Picard.FieldMumfordPointComparisonProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedTrivialPullback
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation
import Langlands.AlgebraicGeometry.Picard.AmpleTensorProof
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Langlands.AlgebraicGeometry.Picard.ProperAmpleTrivialFiniteProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof

/-! # Finitely many rational translations preserve an ample line bundle -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme.TranslationStabilizer

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AbelianScheme.MumfordPicardZero (pullbackTensorIso pullbackCompIso tensorIsoOf)
open Langlands.AbelianScheme.FieldMumfordPoint (pointMap pointMap_fst pointMap_snd)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- Inversion on `A`, the inverse of the identity point. -/
abbrev inversion : A.X ⟶ A.X := (𝟙 A.X)⁻¹

lemma inversion_inversion : inversion A ≫ inversion A = 𝟙 A.X := by
  rw [GrpObj.comp_inv, Category.comp_id, inv_inv]

instance : IsIso (inversion A).left :=
  ⟨(inversion A).left, congrArg CommaMorphism.left (inversion_inversion A),
    congrArg CommaMorphism.left (inversion_inversion A)⟩

variable {Z : Scheme.{u}} (j : Z ⟶ A.X.left)

/-- The scheme `Z` as a test object over the base through `j`. -/
abbrev testObject : Over S := Over.mk (j ≫ A.X.hom)

/-- The tautological point `j` of `A` with values in `Z`. -/
def tautological : testObject A j ⟶ A.X := Over.homMk j

lemma tautological_inversion :
    tautological A j ≫ inversion A = (tautological A j)⁻¹ := by
  rw [GrpObj.comp_inv, Category.comp_id]

/-- The section `z ↦ (z, -j z)` of `Z ×_S A → Z`. -/
def antidiagonal : Z ⟶ (relativeSpace A.X.hom).obj (testObject A j) :=
  pullback.lift (𝟙 Z) (tautological A j ≫ inversion A).left (by
    rw [Over.w, Category.id_comp])

/-- The point `z ↦ (j z, -j z)` of the self-product. -/
abbrev antidiagonalPoint : Z ⟶ pullback A.X.hom A.X.hom :=
  antidiagonal A j ≫ pointMap A (tautological A j)

lemma antidiagonalPoint_fst :
    antidiagonalPoint A j ≫ pullback.fst A.X.hom A.X.hom = j := by
  rw [Category.assoc, pointMap_fst, antidiagonal, pullback.lift_fst_assoc, Category.id_comp]
  rfl

lemma antidiagonalPoint_snd :
    antidiagonalPoint A j ≫ pullback.snd A.X.hom A.X.hom =
      (tautological A j ≫ inversion A).left := by
  rw [Category.assoc, pointMap_snd, antidiagonal, pullback.lift_snd]

/-- Addition restricted to the antidiagonal is the constant identity section. -/
lemma antidiagonalPoint_addition :
    antidiagonalPoint A j ≫ mumfordAddition A = (j ≫ A.X.hom) ≫ unitSection A := by
  let φ : testObject A j ⟶ mumfordProduct A := Over.homMk (antidiagonalPoint A j) (by
    change antidiagonalPoint A j ≫ pullback.fst A.X.hom A.X.hom ≫ A.X.hom = _
    rw [← Category.assoc, antidiagonalPoint_fst]
    rfl)
  have h₁ : φ ≫ mumfordFirst A = tautological A j := by
    apply Over.OverMorphism.ext
    exact antidiagonalPoint_fst A j
  have h₂ : φ ≫ mumfordSecond A = (tautological A j)⁻¹ := by
    rw [← tautological_inversion]
    apply Over.OverMorphism.ext
    exact antidiagonalPoint_snd A j
  have key : φ ≫ (mumfordFirst A * mumfordSecond A) =
      Over.mkIdTerminal.from (testObject A j) ≫ (1 : Over.mk (𝟙 S) ⟶ A.X) := by
    rw [MonObj.comp_mul, h₁, h₂, mul_inv_cancel, MonObj.comp_one]
  have key' := congrArg (fun f ↦ Over.Hom.left f) key
  simp only [φ, Over.comp_left, Over.homMk_left, Over.mkIdTerminal_from_left,
    Over.mk_hom] at key'
  exact key'

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (M : RigidifiedLineBundle (unitSection A)) (L : LineBundle A.X.left)
  (evaluation : tensorObj M.obj.carrier L.obj ≅ structureSheaf A.X.left)

/-- Restricting the Mumford bundle of `M` to the antidiagonal gives `j^*L ⊗ (-j)^*L`;
the addition factor is trivialized by the rigidification of `M`. -/
def antidiagonalMumfordIso :
    (Scheme.Modules.pullback (antidiagonalPoint A j)).obj
      (tensorObj (tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj M.obj.carrier)
          ((Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj L.obj))
        ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj L.obj)) ≅
      tensorObj ((Scheme.Modules.pullback j).obj L.obj)
        ((Scheme.Modules.pullback (tautological A j ≫ inversion A).left).obj L.obj) :=
  let k := antidiagonalPoint A j
  pullbackTensorIso preservation k _ _ ≪≫
    tensorIsoOf
      (pullbackTensorIso preservation k _ _ ≪≫
        tensorIsoOf
          ((Scheme.Modules.pullbackComp k (mumfordAddition A)).app M.obj.carrier ≪≫
            pullbackCompIso (j ≫ A.X.hom) (unitSection A) _
              (antidiagonalPoint_addition A j).symm M.obj.carrier ≪≫
            (Scheme.Modules.pullback (j ≫ A.X.hom)).mapIso M.obj.rigidification.symm ≪≫
            pullbackUnitIso (j ≫ A.X.hom))
          ((Scheme.Modules.pullbackComp k (pullback.fst A.X.hom A.X.hom)).app L.obj ≪≫
            (Scheme.Modules.pullbackCongr (antidiagonalPoint_fst A j)).app L.obj) ≪≫
        tensorLeftUnitor _)
      ((Scheme.Modules.pullbackComp k (pullback.snd A.X.hom A.X.hom)).app L.obj ≪≫
        (Scheme.Modules.pullbackCongr (antidiagonalPoint_snd A j)).app L.obj)

/-- If the Mumford family of `M` and the trivial family agree after pullback along the
tautological point of `Z`, then `j^*L ⊗ (-j)^*L` is trivial. -/
def antidiagonalTrivialization
    (E : (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
        (tautological A j)).obj (mumfordBundle A preservation M L evaluation) ≅
      (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
        (tautological A j)).obj (RigidifiedLineBundle.trivial _)) :
    tensorObj ((Scheme.Modules.pullback j).obj L.obj)
        ((Scheme.Modules.pullback (tautological A j ≫ inversion A).left).obj L.obj) ≅
      structureSheaf Z :=
  (antidiagonalMumfordIso A j preservation M L).symm ≪≫
    ((Scheme.Modules.pullbackComp (antidiagonal A j) (pointMap A (tautological A j))).app
      _).symm ≪≫
    (Scheme.Modules.pullback (antidiagonal A j)).mapIso
      ((LineBundle.forget _).mapIso ((RigidifiedLineBundle.forget _).mapIso
        (E ≪≫ RigidifiedLineBundle.pullbackTrivialIso _ _ _))) ≪≫
    pullbackUnitIso (antidiagonal A j)

end Langlands.AbelianScheme.TranslationStabilizer

namespace Langlands.AbelianScheme.TranslationStabilizer

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AbelianScheme.MumfordPicardZero (tensorIsoOf)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K : Type u) [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- The restriction of a rational point to the trivial base change lies over the point. -/
lemma baseChangeSection_left_fst (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) :
    (GroupScheme.baseChangeSection (𝟙 _) A.toGrp x).left ≫ pullback.fst A.X.hom (𝟙 _) =
      x.left := by
  have h := congrArg (fun y ↦ y.left)
    ((GroupScheme.baseChangePointsEquiv (𝟙 _) A.toGrp (Over.mk (𝟙 _))).apply_symm_apply
      (Over.mkIdTerminal.from _ ≫ x))
  simp only [GroupScheme.baseChangePointsEquiv_left, Over.comp_left,
    Over.mkIdTerminal_from_left] at h
  rw [GroupScheme.baseChangeSection]
  simpa using h

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (M : RigidifiedLineBundle (unitSection A)) (L : LineBundle A.X.left)
  (evaluation : tensorObj M.obj.carrier L.obj ≅ structureSheaf A.X.left)

/-- At a rational point `x` with `t_x^*L ≅ L`, the bundle `t_x^*M ⊗ L` on the trivial
base change is trivial, because `M ⊗ L` is. -/
def pointPremise (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X)
    (e : (LineBundle.pullback (GroupScheme.translation A.toGrp x).left).obj L ≅ L) :
    LineBundle.tensor preservation
        ((LineBundle.pullback (GroupScheme.translation ((baseChange (𝟙 _)).obj A).toGrp
            (GroupScheme.baseChangeSection (𝟙 _) A.toGrp x)).left).obj
          ((LineBundle.pullback (pullback.fst A.X.hom (𝟙 _))).obj
            ((RigidifiedLineBundle.forget (unitSection A)).obj M)))
        ((LineBundle.pullback (pullback.fst A.X.hom (𝟙 _))).obj L) ≅
      familyLineBundle A (T := Over.mk (𝟙 _)) (RigidifiedLineBundle.trivial _) :=
  let p := pullback.fst A.X.hom (𝟙 (Spec (CommRingCat.of K)))
  let t := (GroupScheme.translation ((baseChange (𝟙 _)).obj A).toGrp
    (GroupScheme.baseChangeSection (𝟙 _) A.toGrp x)).left
  ObjectProperty.isoMk _
    (tensorIsoOf (Iso.refl _)
        ((LineBundle.forget _).mapIso ((LineBundle.pullback p).mapIso e.symm ≪≫
          GroupScheme.fibreTranslationIso (𝟙 _) A.toGrp x L)) ≪≫
      pullbackTensorEvaluation preservation t _ _
        (pullbackTensorEvaluation preservation p _ _ evaluation) ≪≫
      (pullbackUnitIso _).symm)

/-- At a rational point `x` with `t_x^*L ≅ L`, the Mumford family of `M` and the trivial
family have the same pulled-back class. -/
lemma mumfordClass_point (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X)
    (hx : Nonempty ((LineBundle.pullback (GroupScheme.translation A.toGrp x).left).obj L ≅ L)) :
    RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) x
        (RigidifiedLineBundle.classOf _ _ _ (mumfordBundle A preservation M L evaluation)) =
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) x
        (RigidifiedLineBundle.classOf _ _ _ (RigidifiedLineBundle.trivial _)) := by
  obtain ⟨e⟩ := hx
  obtain ⟨E⟩ := fieldMumfordPointComparison preservation K A M L evaluation K (𝟙 _) x
    (GroupScheme.baseChangeSection (𝟙 _) A.toGrp x) (baseChangeSection_left_fst K A x)
    (RigidifiedLineBundle.trivial _) ⟨pointPremise K A preservation M L evaluation x e⟩
  exact Quotient.sound ⟨E ≪≫ (RigidifiedLineBundle.pullbackTrivialIso _ _ _).symm⟩

end Langlands.AbelianScheme.TranslationStabilizer

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules TranslationStabilizer

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The agreement locus of the Mumford family of an inverse of `L` with the trivial family
is a closed subscheme `Z` of `A` through which every stabilizing rational point factors and
on which `L ⊗ (-1)^*L` is trivial. -/
theorem stabilizer_equalizer_locus (equalizer : RigidifiedClassesEqualizerClosedStatement.{u})
    (K : Type u) [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))
    (L : LineBundle A.X.left) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ A.X.left), IsClosedImmersion i ∧
      Nonempty (Langlands.Scheme.Modules.tensorObj ((LineBundle.pullback i).obj L).obj
          ((LineBundle.pullback (i ≫ (GrpObj.inv (X := A.X)).left)).obj L).obj ≅
        SheafOfModules.unit Z.ringCatSheaf) ∧
      ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X,
        Nonempty ((LineBundle.pullback (GroupScheme.translation A.toGrp x).left).obj L ≅ L) →
          ∃ g : Spec (CommRingCat.of K) ⟶ Z, g ≫ i = x.left := by
  have preservation : pullbackTensorComparisonIsIsoStatement.{u} :=
    pullbackTensorComparisonIsIso
  obtain ⟨M₀, ⟨ev₀⟩⟩ := L.exists_tensorObj_iso_structureSheaf
  let α := (fieldLineBundleTriviality K ((LineBundle.pullback (unitSection A)).obj M₀)).some
  let M : RigidifiedLineBundle (unitSection A) := RigidifiedLineBundle.ofLineBundle M₀ α.symm
  let evaluation : tensorObj M.obj.carrier L.obj ≅ structureSheaf A.X.left :=
    tensorComm _ _ ≪≫ ev₀
  obtain ⟨Z, j, hj, hZ⟩ := equalizer _ A A.X
    (RigidifiedLineBundle.classOf _ _ _ (mumfordBundle A preservation M L evaluation))
    (RigidifiedLineBundle.classOf _ _ _ (RigidifiedLineBundle.trivial _))
  refine ⟨Z, j, hj, ?_, fun x hx ↦ (hZ (Over.mk (𝟙 _)) x).mpr
    (mumfordClass_point K A preservation M L evaluation x hx)⟩
  obtain ⟨E⟩ := Quotient.exact ((hZ (testObject A j) (tautological A j)).mp
    ⟨𝟙 Z, Category.id_comp j⟩)
  have h : (tautological A j ≫ inversion A).left = j ≫ (GrpObj.inv (X := A.X)).left := by
    rw [Over.comp_left, inversion, ← GrpObj.inv_eq_inv]
    rfl
  rw [← h]
  exact ⟨antidiagonalTrivialization A j preservation M L evaluation E⟩

/-- If every stabilizing rational point factors through a closed subscheme `Z` on which
`L ⊗ (-1)^* L` restricts to the trivial bundle, then the stabilizer is finite. -/
theorem stabilizer_finite_of_locus (K : Type u) [Field K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (L : LineBundle A.X.left) (hL : L.IsAmple)
    (Z : Scheme.{u}) (i : Z ⟶ A.X.left) [IsClosedImmersion i]
    (hN : Nonempty (Langlands.Scheme.Modules.tensorObj ((LineBundle.pullback i).obj L).obj
        ((LineBundle.pullback (i ≫ (GrpObj.inv (X := A.X)).left)).obj L).obj ≅
      SheafOfModules.unit Z.ringCatSheaf))
    (hZ : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X,
      Nonempty ((LineBundle.pullback (GroupScheme.translation A.toGrp x).left).obj L ≅ L) →
        ∃ g : Spec (CommRingCat.of K) ⟶ Z, g ≫ i = x.left) :
    Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X //
      Nonempty ((LineBundle.pullback (GroupScheme.translation A.toGrp x).left).obj L ≅ L)} := by
  have : IsIso (GrpObj.inv (X := A.X)).left := (Over.forget _).map_isIso _
  have h₁ := closedImmersionPullbackAmple _ _ i L inferInstance hL
  have h₂ := closedImmersionPullbackAmple _ _ (i ≫ (GrpObj.inv (X := A.X)).left) L
    inferInstance hL
  have hT : (LineBundle.trivial Z).IsAmple := ampleTensor Z _ _ _ hN h₁ h₂
  have : IsFinite (i ≫ A.X.hom) :=
    properAmpleTrivialFinite K Z (i ≫ A.X.hom) (LineBundle.trivial Z) inferInstance hT
      ⟨Iso.refl _⟩
  let F : {x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X //
      Nonempty ((LineBundle.pullback (GroupScheme.translation A.toGrp x).left).obj L ≅ L)} →
      {g : Spec (CommRingCat.of K) ⟶ Z // g ≫ i ≫ A.X.hom = 𝟙 _} := fun x ↦
    ⟨(hZ x.1 x.2).choose, by
      rw [← Category.assoc, (hZ x.1 x.2).choose_spec]
      exact Over.w x.1⟩
  have := Langlands.AlgebraicGeometry.FiniteEtale.finite_sections_of_isFinite
    (K := K) (i ≫ A.X.hom)
  refine Finite.of_injective F (fun x y e ↦ Subtype.ext (Over.OverMorphism.ext ?_))
  rw [← (hZ x.1 x.2).choose_spec, ← (hZ y.1 y.2).choose_spec]
  exact congrArg (fun g ↦ g.1 ≫ i) e

/-- Conditional on the closed agreement locus, finitely many rational translations preserve
an ample line bundle; algebraic closure of `K` is not used. -/
theorem algClosedFieldAmpleTranslationStabilizerFinite_of_equalizer
    (equalizer : RigidifiedClassesEqualizerClosedStatement.{u}) :
    AlgClosedFieldAmpleTranslationStabilizerFiniteStatement.{u} := by
  intro K _ _ A L hL
  obtain ⟨Z, i, hi, hN, hZ⟩ := stabilizer_equalizer_locus equalizer K A L
  have := hi
  exact stabilizer_finite_of_locus K A L hL Z i hN hZ

/-- Finitely many rational translations of an abelian variety over an algebraically closed
field preserve an ample line bundle. -/
theorem algClosedFieldAmpleTranslationStabilizerFinite :
    AlgClosedFieldAmpleTranslationStabilizerFiniteStatement.{u} :=
  algClosedFieldAmpleTranslationStabilizerFinite_of_equalizer rigidifiedClassesEqualizerClosed

end Langlands.AbelianScheme
