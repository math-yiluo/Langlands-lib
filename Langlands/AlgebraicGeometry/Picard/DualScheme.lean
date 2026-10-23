import Langlands.AlgebraicGeometry.Picard.PicardZeroUniversalBundle

/-! # A chosen dual scheme from the actual universal bundle property -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- Existence of a parameter scheme with an actual universal Picard-zero family. -/
def HasDualScheme : Prop :=
  ∃ (P : Over S) (L : RigidifiedFamily A P), IsUniversalPicardZero A L

/-- Choose the parameter scheme from a proof of the actual existence proposition. -/
def dualScheme (hA : HasDualScheme A) : Over S :=
  Classical.choose hA

/-- The chosen rigidified Poincaré family, on `dualScheme ×_S A`. -/
def poincareFamily (hA : HasDualScheme A) : RigidifiedFamily A (dualScheme A hA) :=
  Classical.choose (Classical.choose_spec hA)

/-- The selected family satisfies the checked universal property. -/
lemma poincareFamily_universal (hA : HasDualScheme A) :
    IsUniversalPicardZero A (poincareFamily A hA) :=
  Classical.choose_spec (Classical.choose_spec hA)

/-- The underlying Poincaré line bundle on the conventional total space `A ×_S dualScheme`. -/
def poincareLineBundle (hA : HasDualScheme A) :
    LineBundle ((baseChange (dualScheme A hA).hom).obj A).X.left :=
  familyLineBundle A (poincareFamily A hA)

lemma poincareLineBundle_picardZero (hA : HasDualScheme A) :
    IsGeometricallyPicardZero ((baseChange (dualScheme A hA).hom).obj A)
      (poincareLineBundle A hA) :=
  (poincareFamily_universal A hA).1

/-- The unique parameter map classifying a specified actual Picard-zero class. -/
def dualClassify (hA : HasDualScheme A) (T : Over S) (q : PicardZeroClasses A T) :
    T ⟶ dualScheme A hA :=
  Classical.choose ((poincareFamily_universal A hA).2 T q)

lemma dualClassify_spec (hA : HasDualScheme A) (T : Over S)
    (q : PicardZeroClasses A T) :
    RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
      (poincareFamily A hA) T (dualClassify A hA T q) = q.val :=
  (Classical.choose_spec ((poincareFamily_universal A hA).2 T q)).1

lemma dualClassify_unique (hA : HasDualScheme A) (T : Over S)
    (q : PicardZeroClasses A T) (f : T ⟶ dualScheme A hA)
    (hf : RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
      (poincareFamily A hA) T f = q.val) :
    f = dualClassify A hA T q :=
  (Classical.choose_spec ((poincareFamily_universal A hA).2 T q)).2 f hf

/-- A representative is classified by actual rigidified pullback, not an arbitrary bijection. -/
def dualClassifyPullbackIso (hA : HasDualScheme A) {T : Over S}
    (L : RigidifiedFamily A T) (hL : IsPicardZeroFamily A L) :
    (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
      (dualClassify A hA T
        ⟨RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) L,
          hL⟩)).obj (poincareFamily A hA) ≅ L :=
  Classical.choice
    ((RigidifiedLineBundle.classifyingMap_eq_iff A.X.hom (unitSection A)
      (unitSection_comp A) (poincareFamily A hA) L _).mp
        (dualClassify_spec A hA T _))

/-- The section of the chosen dual classifying the canonically rigidified trivial bundle. -/
def dualOrigin (hA : HasDualScheme A) : Over.mk (𝟙 S) ⟶ dualScheme A hA :=
  dualClassify A hA (Over.mk (𝟙 S)) (trivialPicardZeroClass A _)

lemma dualOrigin_spec (hA : HasDualScheme A) :
    RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
      (poincareFamily A hA) (Over.mk (𝟙 S)) (dualOrigin A hA) =
        (trivialPicardZeroClass A (Over.mk (𝟙 S))).val :=
  dualClassify_spec A hA _ _

variable (coherence : RigidifiedModule.PullbackCoherenceStatement.{u})

include coherence in
/-- Classifying the Poincaré family itself gives the identity of its parameter scheme. -/
lemma dualClassify_poincare (hA : HasDualScheme A) :
    dualClassify A hA (dualScheme A hA)
      ⟨RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
        (poincareFamily A hA), (poincareFamily_universal A hA).1⟩ =
      𝟙 (dualScheme A hA) := by
  symm
  apply dualClassify_unique
  exact RigidifiedLineBundle.classifyingMap_id A.X.hom
    (unitSection A) (unitSection_comp A) coherence _

variable (stability : PicardZeroPullbackStatement.{u})

/-- The chosen dual represents the actual Picard-zero presheaf under explicit compatibility proofs. -/
def dualSchemeRepresentableBy (hA : HasDualScheme A) :
    (picardZeroPresheaf stability A coherence).RepresentableBy (dualScheme A hA) :=
  picardZeroRepresentableBy A stability coherence
    (poincareFamily A hA) (poincareFamily_universal A hA)

include coherence in
/-- Classification commutes with the actual restricted pullback in the parameter scheme. -/
lemma dualClassify_pullback (hA : HasDualScheme A) {T U : Over S}
    (f : T ⟶ U) (q : PicardZeroClasses A U) :
    dualClassify A hA T (picardZeroClassesPullback stability A f q) =
      f ≫ dualClassify A hA U q := by
  symm
  apply dualClassify_unique
  rw [RigidifiedLineBundle.classifyingMap_comp A.X.hom
    (unitSection A) (unitSection_comp A) coherence, dualClassify_spec]
  rfl

end Langlands.AbelianScheme
