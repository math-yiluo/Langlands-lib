import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackStatement
import Mathlib.CategoryTheory.Subfunctor.Basic

/-! # The geometric Picard-zero subfunctor -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

variable (stability : PicardZeroPullbackStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S)

include stability in
/-- Pullback preserves the geometric-fibre condition on rigidified isomorphism classes. -/
lemma isPicardZeroClass_pullback {T U : Over S} (h : T ⟶ U)
    (q : RigidifiedClasses A U) (hq : IsPicardZeroClass A q) :
    IsPicardZeroClass A
      (RigidifiedLineBundle.classesPullback A.X.hom
        (unitSection A) (unitSection_comp A) h q) := by
  induction q using Quotient.inductionOn with
  | h L => exact stability S A T U h L hq

/-- Restrict the actual pullback on rigidified classes to the geometric Picard-zero subset. -/
def picardZeroClassesPullback {T U : Over S} (h : T ⟶ U) :
    PicardZeroClasses A U → PicardZeroClasses A T :=
  fun q ↦ ⟨RigidifiedLineBundle.classesPullback A.X.hom
    (unitSection A) (unitSection_comp A) h q.val,
    isPicardZeroClass_pullback stability A h q.val q.property⟩

variable (coherence : RigidifiedModule.PullbackCoherenceStatement.{u})

/-- The geometric-fibre subsets form a subfunctor, with both compatibility proofs explicit. -/
def picardZeroSubfunctor :
    Subfunctor (RigidifiedLineBundle.classPresheaf coherence A.X.hom
      (unitSection A) (unitSection_comp A)) where
  obj _ := {q | IsPicardZeroClass A q}
  map h _ hq := isPicardZeroClass_pullback stability A h.unop _ hq

/-- The presheaf of rigidified classes satisfying the geometric-fibre Picard-zero condition. -/
def picardZeroPresheaf : (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  (picardZeroSubfunctor stability A coherence).toFunctor

/-- The inclusion of the Picard-zero presheaf into all rigidified line-bundle classes. -/
def picardZeroInclusion :
    picardZeroPresheaf stability A coherence ⟶
      RigidifiedLineBundle.classPresheaf coherence A.X.hom
        (unitSection A) (unitSection_comp A) :=
  (picardZeroSubfunctor stability A coherence).ι

instance : Mono (picardZeroInclusion stability A coherence) :=
  inferInstanceAs (Mono (picardZeroSubfunctor stability A coherence).ι)

/-- The presheaf restriction is the restricted actual rigidified pullback. -/
@[simp] lemma picardZeroPresheaf_map {T U : Over S} (h : T ⟶ U)
    (q : PicardZeroClasses A U) :
    (picardZeroPresheaf stability A coherence).map h.op q =
      picardZeroClassesPullback stability A h q := rfl

/-- At every test scheme the inclusion forgets only the membership proof. -/
@[simp] lemma picardZeroInclusion_app (T : Over S) (q : PicardZeroClasses A T) :
    (picardZeroInclusion stability A coherence).app (op T) q = q.val := rfl

end Langlands.AbelianScheme
