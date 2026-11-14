import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleTranslationStabilizerFiniteProof
import Langlands.AlgebraicGeometry.Picard.MumfordParameterAxes
import Langlands.AbelianScheme.FieldAmpleExistenceProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedForgetLocallySurjective
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassMonoid

/-! # A finite closed locus where a Mumford family is trivial -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme.FieldMumfordFiniteLocus

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules TranslationStabilizer

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Over any field, an abelian variety carries a rigidified family `q` over its own parameter
space, trivial at the unit parameter, together with a closed subscheme `Z`, finite over the
field, through which a test point factors exactly when `q` pulls back to the trivial class. -/
theorem exists_finite_locus (K : Type u) [Field K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) :
    ∃ (q : RigidifiedClasses A A.X) (Z : Scheme.{u}) (j : Z ⟶ A.X.left),
      IsClosedImmersion j ∧ IsFinite (j ≫ A.X.hom) ∧
      (∀ T : Over (Spec (CommRingCat.of K)),
        RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
            (1 : T ⟶ A.X) q =
          RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
            (RigidifiedLineBundle.trivial
              ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T))) ∧
      ∀ (T : Over (Spec (CommRingCat.of K))) (h : T ⟶ A.X),
        (∃ g : T.left ⟶ Z, g ≫ j = h.left) ↔
          RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
              h q =
            RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
              h (RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
                (RigidifiedLineBundle.trivial
                  ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app A.X))) := by
  have preservation : pullbackTensorComparisonIsIsoStatement.{u} :=
    pullbackTensorComparisonIsIso
  obtain ⟨L, hL⟩ := Langlands.GroupScheme.fieldAmpleExistence K A.toGrp
    inferInstance inferInstance inferInstance
  obtain ⟨M₀, ⟨ev₀⟩⟩ := L.exists_tensorObj_iso_structureSheaf
  let α := (fieldLineBundleTriviality K ((LineBundle.pullback (unitSection A)).obj M₀)).some
  let M : RigidifiedLineBundle (unitSection A) := RigidifiedLineBundle.ofLineBundle M₀ α.symm
  let evaluation : tensorObj M.obj.carrier L.obj ≅ structureSheaf A.X.left :=
    tensorComm _ _ ≪≫ ev₀
  obtain ⟨Z, j, hj, hZ⟩ := rigidifiedClassesEqualizerClosed _ A A.X
    (RigidifiedLineBundle.classOf _ _ _ (mumfordBundle A preservation M L evaluation))
    (RigidifiedLineBundle.classOf _ _ _ (RigidifiedLineBundle.trivial _))
  have := hj
  obtain ⟨E⟩ := Quotient.exact ((hZ (testObject A j) (tautological A j)).mp
    ⟨𝟙 Z, Category.id_comp j⟩)
  have hinv : (tautological A j ≫ inversion A).left = j ≫ (GrpObj.inv (X := A.X)).left := by
    rw [Over.comp_left, inversion, ← GrpObj.inv_eq_inv]
    rfl
  have hN : Nonempty (Langlands.Scheme.Modules.tensorObj ((LineBundle.pullback j).obj L).obj
      ((LineBundle.pullback (j ≫ (GrpObj.inv (X := A.X)).left)).obj L).obj ≅
        SheafOfModules.unit Z.ringCatSheaf) := by
    rw [← hinv]
    exact ⟨antidiagonalTrivialization A j preservation M L evaluation E⟩
  have : IsIso (GrpObj.inv (X := A.X)).left := (Over.forget _).map_isIso _
  have h₁ := closedImmersionPullbackAmple _ _ j L inferInstance hL
  have h₂ := closedImmersionPullbackAmple _ _ (j ≫ (GrpObj.inv (X := A.X)).left) L
    inferInstance hL
  have hT : (LineBundle.trivial Z).IsAmple := ampleTensor Z _ _ _ hN h₁ h₂
  have hfin : IsFinite (j ≫ A.X.hom) :=
    properAmpleTrivialFinite K Z (j ≫ A.X.hom) (LineBundle.trivial Z) inferInstance hT
      ⟨Iso.refl _⟩
  exact ⟨_, Z, j, hj, hfin, mumfordBundleClass_one A preservation M L evaluation, hZ⟩

section Plain

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)

/-- Forgetting the rigidification commutes with pullback of classes. -/
lemma forgetClasses_classesPullback {T U : Over S} (h : T ⟶ U)
    (q : RigidifiedLineBundle.Classes f ε section_eq U) :
    RigidifiedLineBundle.forgetClasses f ε section_eq T
        (RigidifiedLineBundle.classesPullback f ε section_eq h q) =
      Langlands.AlgebraicGeometry.Picard.Group.pullback ((relativeSpace f).map h)
        (RigidifiedLineBundle.forgetClasses f ε section_eq U q) := by
  refine Quotient.inductionOn q (fun L ↦ ?_)
  change RelativePicard.classOf f T ((RigidifiedLineBundle.forget _).obj
      ((RigidifiedLineBundle.relativePullback f ε section_eq h).obj L)) =
    (RelativePicard.classPresheaf f).map h.op
      (RelativePicard.classOf f U ((RigidifiedLineBundle.forget _).obj L))
  rw [RelativePicard.map_classOf]
  exact (RelativePicard.classOf_eq_iff_iso f T _ _).2
    ⟨(RigidifiedLineBundle.pullbackForgetIso ((relativeSpace f).map h) h.left
      ((relativeSection f ε section_eq).naturality h).symm).app L⟩

/-- The trivial rigidified class forgets to the zero class. -/
lemma forgetClasses_trivialClass (T : Over S) :
    RigidifiedLineBundle.forgetClasses f ε section_eq T
      (RigidifiedLineBundle.trivialClass f ε section_eq T) =
        (0 : Langlands.AlgebraicGeometry.Picard.Group ((relativeSpace f).obj T)) :=
  RelativePicard.classOf_trivial f T

end Plain

/-- Over any field, an abelian variety carries an ordinary relative Picard class `Q` over its
own parameter space, vanishing at the unit parameter, together with a closed subscheme `Z`,
finite over the field, through which a test point factors exactly when `Q` pulls back to
zero. -/
theorem exists_finite_plain_locus (K : Type u) [Field K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) :
    ∃ (Q : Langlands.AlgebraicGeometry.Picard.Group ((relativeSpace A.X.hom).obj A.X))
      (Z : Scheme.{u}) (j : Z ⟶ A.X.left),
      IsClosedImmersion j ∧ IsFinite (j ≫ A.X.hom) ∧
      (∀ T : Over (Spec (CommRingCat.of K)),
        Langlands.AlgebraicGeometry.Picard.Group.pullback
          ((relativeSpace A.X.hom).map (1 : T ⟶ A.X)) Q = 0) ∧
      ∀ (T : Over (Spec (CommRingCat.of K))) (h : T ⟶ A.X),
        (∃ g : T.left ⟶ Z, g ≫ j = h.left) ↔
          Langlands.AlgebraicGeometry.Picard.Group.pullback ((relativeSpace A.X.hom).map h) Q =
            0 := by
  obtain ⟨q, Z, j, hj, hfin, hq1, hZ⟩ := exists_finite_locus K A
  refine ⟨RigidifiedLineBundle.forgetClasses A.X.hom (unitSection A) (unitSection_comp A) A.X q,
    Z, j, hj, hfin, fun T ↦ ?_, fun T h ↦ ?_⟩
  · rw [← forgetClasses_classesPullback, hq1]
    exact forgetClasses_trivialClass _ _ _ T
  · rw [hZ T h, ← forgetClasses_classesPullback]
    have htriv := RigidifiedLineBundle.classesPullback_trivialClass A.X.hom (unitSection A)
      (unitSection_comp A) h
    change _ = RigidifiedLineBundle.classesPullback _ _ _ h
      (RigidifiedLineBundle.trivialClass _ _ _ A.X) ↔ _
    rw [htriv, ← forgetClasses_trivialClass A.X.hom (unitSection A) (unitSection_comp A) T]
    exact (RigidifiedLineBundle.forgetClasses_injective _ _ _ T).eq_iff.symm

end Langlands.AbelianScheme.FieldMumfordFiniteLocus
