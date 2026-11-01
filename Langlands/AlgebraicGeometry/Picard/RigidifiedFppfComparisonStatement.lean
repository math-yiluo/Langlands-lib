import Langlands.AlgebraicGeometry.Picard.RelativePicardSheaf
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs
import Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalBundle
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # The canonical rigidified-class comparison with the fppf Picard sheaf -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule

namespace RigidifiedLineBundle

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X)
  (section_eq : ε ≫ f = 𝟙 S)

/-- Forget the rigidification on actual isomorphism classes. -/
def forgetClasses (T : Over S) :
    Classes f ε section_eq T → (RelativePicard.classPresheaf f).obj (op T) :=
  Quotient.lift
    (fun L ↦ RelativePicard.classOf f T
      ((forget ((relativeSection f ε section_eq).app T)).obj L))
    (by
      intro L M h
      obtain ⟨e⟩ := h
      exact (RelativePicard.classOf_eq_iff_iso f T _ _).2
        ⟨(forget _).mapIso e⟩)

@[simp]
lemma forgetClasses_classOf (T : Over S) (L : relative f ε section_eq T) :
    forgetClasses f ε section_eq T (classOf f ε section_eq L) =
      RelativePicard.classOf f T
        ((forget ((relativeSection f ε section_eq).app T)).obj L) := rfl

/-- Forgetting rigidification commutes with the actual geometric pullbacks. -/
def forgetClassNatTrans :
    classPresheaf RigidifiedModule.pullbackCoherence f ε section_eq ⟶
      RelativePicard.classPresheaf f where
  app T := TypeCat.ofHom (forgetClasses f ε section_eq T.unop)
  naturality {T U} h := by
    ext q
    refine Quotient.inductionOn q (fun L ↦ ?_)
    change RelativePicard.classOf f U.unop
        ((forget _).obj ((relativePullback f ε section_eq h.unop).obj L)) =
      (RelativePicard.classPresheaf f).map h.unop.op
        (RelativePicard.classOf f T.unop ((forget _).obj L))
    rw [RelativePicard.map_classOf]
    exact (RelativePicard.classOf_eq_iff_iso f U.unop _ _).2
      ⟨(pullbackForgetIso ((relativeSpace f).map h.unop) h.unop.left
        ((relativeSection f ε section_eq).naturality h.unop).symm).app L⟩

/-- The canonical map to the underlying presheaf of the abelian-group Picard sheaf. -/
def toPicardSheaf :
    classPresheaf RigidifiedModule.pullbackCoherence f ε section_eq ⟶
      RelativePicard.sheafPresheaf f ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1} :=
  forgetClassNatTrans f ε section_eq ≫
    Functor.whiskerRight (RelativePicard.toSheaf f)
      (CategoryTheory.forget AddCommGrpCat.{u + 1})

/-- The same canonical map using the actual set-valued sheafification. -/
def toClassPicardSheaf :
    classPresheaf RigidifiedModule.pullbackCoherence f ε section_eq ⟶
      RelativePicard.classSheafPresheaf f :=
  forgetClassNatTrans f ε section_eq ≫ RelativePicard.toClassSheaf f

@[simp]
lemma toPicardSheaf_app_classOf (T : Over S) (L : relative f ε section_eq T) :
    (toPicardSheaf f ε section_eq).app (op T) (classOf f ε section_eq L) =
      (RelativePicard.toSheaf f).app (op T)
        (RelativePicard.classOf f T
          ((forget ((relativeSection f ε section_eq).app T)).obj L)) := rfl

@[simp]
lemma toClassPicardSheaf_app_classOf (T : Over S) (L : relative f ε section_eq T) :
    (toClassPicardSheaf f ε section_eq).app (op T) (classOf f ε section_eq L) =
      RelativePicard.sheafClassOf f T
        ((forget ((relativeSection f ε section_eq).app T)).obj L) := rfl

/-- The group/set sheaf comparison identifies the two specified canonical maps. -/
@[reassoc (attr := simp)]
lemma toPicardSheaf_forgetSheafIso_hom :
    toPicardSheaf f ε section_eq ≫ (RelativePicard.forgetSheafIso f).hom =
      toClassPicardSheaf f ε section_eq := by
  exact congrArg (fun η ↦ forgetClassNatTrans f ε section_eq ≫ η)
    (RelativePicard.toSheaf_forgetSheafIso_hom f)

/-- The component formula is compatible with pullback along every test-scheme morphism. -/
lemma map_toPicardSheaf_classOf {T U : Over S} (h : T ⟶ U)
    (L : relative f ε section_eq U) :
    (RelativePicard.sheafPresheaf f ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).map h.op
        ((toPicardSheaf f ε section_eq).app (op U) (classOf f ε section_eq L)) =
      (toPicardSheaf f ε section_eq).app (op T)
        (classOf f ε section_eq ((relativePullback f ε section_eq h).obj L)) :=
  ((toPicardSheaf f ε section_eq).naturality_apply h.op (classOf f ε section_eq L)).symm

end RigidifiedLineBundle

/-- Under the universal canonical structure-sheaf condition and a section, the canonical
forget-rigidification map identifies rigidified classes with the actual fppf Picard sheaf. -/
def RigidifiedFppfComparisonStatement : Prop :=
  ∀ (S X : Scheme.{u}) (f : X ⟶ S),
    QuasiCompact f → QuasiSeparated f →
    ∀ (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S),
      (∀ (T : Over S) (U : T.left.Opens),
        IsIso (((relativeProjection f).app T).app U)) →
      IsIso (RigidifiedLineBundle.toPicardSheaf f ε section_eq)

end Langlands.AlgebraicGeometry.Picard
