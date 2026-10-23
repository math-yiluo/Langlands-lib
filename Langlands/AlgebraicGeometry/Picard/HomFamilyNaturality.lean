import Langlands.AlgebraicGeometry.Picard.HomPicardZeroPullbackStatement
import Langlands.AlgebraicGeometry.Picard.PicardZeroSubfunctor

/-! # Naturality of homomorphism pullback in the parameter scheme -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

variable {S : Scheme.{u}} {A B C : AbelianScheme S}
variable (coherence : RigidifiedModule.PullbackCoherenceStatement.{u})

/-- Pullback along a homomorphism commutes with pullback in the parameter scheme. -/
def homFamilyPullbackNaturality (f : A ⟶ B) {T U : Over S} (h : T ⟶ U) :
    homFamilyPullback f U ⋙
        RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A) h ≅
      RigidifiedLineBundle.relativePullback B.X.hom (unitSection B) (unitSection_comp B) h ⋙
        homFamilyPullback f T := by
  let i₁ := RigidifiedLineBundle.pullbackComp coherence
    (ε := (relativeSection B.X.hom (unitSection B) (unitSection_comp B)).app U)
    (ε' := (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app U)
    (ε'' := (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T)
    ((homFamilySpaceMap f).app U) (𝟙 U.left)
    ((relativeSpace A.X.hom).map h) h.left
    (by simp) ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).naturality h).symm
    (by
      rw [← Category.assoc,
        ← (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).naturality h]
      simp [Category.assoc])
  let i₂ := RigidifiedLineBundle.pullbackComp coherence
    (ε := (relativeSection B.X.hom (unitSection B) (unitSection_comp B)).app U)
    (ε' := (relativeSection B.X.hom (unitSection B) (unitSection_comp B)).app T)
    (ε'' := (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T)
    ((relativeSpace B.X.hom).map h) h.left
    ((homFamilySpaceMap f).app T) (𝟙 T.left)
    ((relativeSection B.X.hom (unitSection B) (unitSection_comp B)).naturality h).symm
    (by simp)
    (by
      rw [← Category.assoc, relativeSection_homFamilySpaceMap]
      exact ((relativeSection B.X.hom (unitSection B) (unitSection_comp B)).naturality h).symm)
  exact i₁ ≪≫
    RigidifiedLineBundle.pullbackCongr ((homFamilySpaceMap f).naturality h)
      ((Category.comp_id _).trans (Category.id_comp _).symm) _ _ ≪≫ i₂.symm

include coherence in
lemma homClassesPullback_naturality (f : A ⟶ B) {T U : Over S} (h : T ⟶ U)
    (q : RigidifiedClasses B U) :
    RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) h
        (homClassesPullback f U q) =
      homClassesPullback f T
        (RigidifiedLineBundle.classesPullback B.X.hom (unitSection B)
          (unitSection_comp B) h q) := by
  refine Quotient.inductionOn q (fun L ↦ ?_)
  exact Quotient.sound ⟨(homFamilyPullbackNaturality coherence f h).app L⟩

/-- Homomorphism pullback as a natural transformation of actual rigidified class presheaves. -/
def homClassesPullbackNatTrans (f : A ⟶ B) :
    RigidifiedLineBundle.classPresheaf coherence B.X.hom (unitSection B) (unitSection_comp B) ⟶
      RigidifiedLineBundle.classPresheaf coherence A.X.hom (unitSection A) (unitSection_comp A) where
  app T := TypeCat.ofHom (homClassesPullback f T.unop)
  naturality {T U} h := by
    ext q
    exact (homClassesPullback_naturality coherence f h.unop q).symm

variable (preservation : HomPicardZeroPullbackStatement.{u})

/-- Restrict the actual class pullback using the explicit preservation proposition. -/
def homPicardZeroClassesPullback (f : A ⟶ B) (T : Over S) :
    PicardZeroClasses B T → PicardZeroClasses A T := fun q ↦
  ⟨homClassesPullback f T q.val, by
    rcases q with ⟨q, hq⟩
    induction q using Quotient.inductionOn with
    | h L => exact preservation S A B f T L hq⟩

include coherence in
lemma homPicardZeroClassesPullback_id (A : AbelianScheme S) (T : Over S)
    (q : PicardZeroClasses A T) :
    homPicardZeroClassesPullback preservation (𝟙 A) T q = q := by
  apply Subtype.ext
  exact homClassesPullback_id coherence A T q.val

include coherence in
lemma homPicardZeroClassesPullback_comp (f : A ⟶ B) (g : B ⟶ C) (T : Over S)
    (q : PicardZeroClasses C T) :
    homPicardZeroClassesPullback preservation (f ≫ g) T q =
      homPicardZeroClassesPullback preservation f T
        (homPicardZeroClassesPullback preservation g T q) := by
  apply Subtype.ext
  exact homClassesPullback_comp coherence f g T q.val

variable (stability : PicardZeroPullbackStatement.{u})

/-- Restriction to the actual geometric Picard-zero presheaves. -/
def homPicardZeroPullbackNatTrans (f : A ⟶ B) :
    picardZeroPresheaf stability B coherence ⟶ picardZeroPresheaf stability A coherence where
  app T := TypeCat.ofHom (homPicardZeroClassesPullback preservation f T.unop)
  naturality {T U} h := by
    ext q
    apply Subtype.ext
    exact (homClassesPullback_naturality coherence f h.unop q.val).symm

end Langlands.AbelianScheme
