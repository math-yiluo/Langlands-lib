import Langlands.AlgebraicGeometry.Picard.FieldIsogenyKernelDescentStatements
import Langlands.AlgebraicGeometry.Picard.HomPicardZeroPullbackProof

/-! # Trivial homomorphism pullbacks on geometric fibres -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} {A B : AbelianScheme S}

/-- The geometric field criterion needed after transporting a trivial
isogeny pullback to an algebraically closed fibre. -/
def AlgClosedFieldTrivialPullbackTranslationInvariantStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A B : AbelianScheme (Spec (CommRingCat.of K))) (f : A ⟶ B),
    IsIsogeny f →
    ∀ L : LineBundle B.X.left,
      Nonempty ((Scheme.Modules.pullback (hom f)).obj L.obj ≅
        SheafOfModules.unit A.X.left.ringCatSheaf) →
      GroupScheme.IsTranslationInvariant B.toGrp L

/-- Changing the product order carries an actual family trivialization to
ordinary pullback along the base-changed homomorphism. -/
lemma homPullback_familyLineBundle_trivial (f : A ⟶ B) (T : Over S)
    (L : RigidifiedFamily B T)
    (hL : HasTrivialHomPullback f T ((RigidifiedLineBundle.forget _).obj L)) :
    Nonempty
      ((Scheme.Modules.pullback (hom ((baseChange T.hom).map f))).obj
          (familyLineBundle B L).obj ≅
        SheafOfModules.unit ((baseChange T.hom).obj A).X.left.ringCatSheaf) := by
  obtain ⟨α⟩ := hL
  exact ⟨(LineBundle.forget _).mapIso (homFamilyLineBundleIso f T L) ≪≫
    (Scheme.Modules.pullback (relativeSpaceSymmetry A.X.hom T).inv).mapIso α ≪≫
      Langlands.Scheme.Modules.pullbackUnitIso _⟩

/-- Ordinary homomorphism-pullback triviality is preserved on every base change,
using the actual first projections of the chosen fibre products. -/
lemma homPullback_fibreLineBundle_trivial (f : A ⟶ B)
    {V : Scheme.{u}} (s : V ⟶ S) (L : LineBundle B.X.left)
    (hL : Nonempty ((Scheme.Modules.pullback (hom f)).obj L.obj ≅
      SheafOfModules.unit A.X.left.ringCatSheaf)) :
    Nonempty
      ((Scheme.Modules.pullback (hom ((baseChange s).map f))).obj
          (fibreLineBundle B L s).obj ≅
        SheafOfModules.unit ((baseChange s).obj A).X.left.ringCatSheaf) := by
  obtain ⟨α⟩ := hL
  have comm : hom ((baseChange s).map f) ≫ pullback.fst B.X.hom s =
      pullback.fst A.X.hom s ≫ hom f := by
    change ((Over.pullback s).map (groupHom f).hom.hom).left ≫ _ = _
    simp
  exact ⟨(Scheme.Modules.pullbackComp _ _).app L.obj ≪≫
    (Scheme.Modules.pullbackCongr comm).app L.obj ≪≫
      ((Scheme.Modules.pullbackComp _ _).app L.obj).symm ≪≫
        (Scheme.Modules.pullback (pullback.fst A.X.hom s)).mapIso α ≪≫
          Langlands.Scheme.Modules.pullbackUnitIso _⟩

/-- A criterion for ordinary line bundles over algebraically closed fields
suffices for the unchanged all-parameter geometric Picard-zero target. -/
theorem fieldTrivialPullbackPicardZero_of_algClosed_translationInvariant
    (h : AlgClosedFieldTrivialPullbackTranslationInvariantStatement.{u}) :
    FieldTrivialPullbackPicardZeroStatement.{u} := by
  intro k _ A B f hf T L hL K _ _ s
  exact h K _ _ ((baseChange s).map ((baseChange T.hom).map f))
    ((hf.baseChange T.hom).baseChange s) _
    (homPullback_fibreLineBundle_trivial _ s _
      (homPullback_familyLineBundle_trivial f T L hL))

end Langlands.AbelianScheme
