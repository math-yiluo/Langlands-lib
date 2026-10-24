import Langlands.AlgebraicGeometry.Picard.PicardZeroUniversalBaseChangeStatement
import Langlands.AlgebraicGeometry.Picard.PicardZeroUniversalUniquenessProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs

/-! # Canonical comparison with the actual base-changed dual scheme -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable (universality : PicardZeroUniversalBaseChangeStatement.{u})
variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S) (hA : HasDualScheme A)

include universality in
/-- The explicit base-changed Poincare family is universal under the named theorem input. -/
lemma poincareFamilyBaseChange_universal :
    IsUniversalPicardZero ((baseChange b).obj A) (poincareFamilyBaseChange b A hA) :=
  universality S S' b A (dualScheme A hA) (poincareFamily A hA)
    (poincareFamily_universal A hA)

include universality hA in
/-- Actual dual-scheme existence after base change, witnessed by the pulled-back parameter
scheme and its constructed family. -/
lemma hasDualScheme_baseChange : HasDualScheme ((baseChange b).obj A) :=
  ⟨(Over.pullback b).obj (dualScheme A hA), poincareFamilyBaseChange b A hA,
    poincareFamilyBaseChange_universal universality b A hA⟩

variable (hA' : HasDualScheme ((baseChange b).obj A))

/-- The uniquely compatible isomorphism from the actual base-changed dual parameter
scheme to any chosen dual of the base-changed abelian scheme. -/
def dualSchemeBaseChangeIso :
    (Over.pullback b).obj (dualScheme A hA) ≅ dualScheme ((baseChange b).obj A) hA' :=
  Classical.choose (picardZeroUniversalUniqueness
    Langlands.SchemeModule.RigidifiedModule.pullbackCoherence S' ((baseChange b).obj A)
    _ _ (poincareFamilyBaseChange b A hA) (poincareFamily ((baseChange b).obj A) hA')
    (poincareFamilyBaseChange_universal universality b A hA)
    (poincareFamily_universal ((baseChange b).obj A) hA'))

/-- The comparison is characterized by an actual rigidified Poincare pullback isomorphism. -/
def dualSchemeBaseChangePullbackIso :
    (RigidifiedLineBundle.relativePullback ((baseChange b).obj A).X.hom
      (unitSection ((baseChange b).obj A)) (unitSection_comp _)
      (dualSchemeBaseChangeIso universality b A hA hA').hom).obj
        (poincareFamily ((baseChange b).obj A) hA') ≅ poincareFamilyBaseChange b A hA :=
  Classical.choice (Classical.choose_spec (picardZeroUniversalUniqueness
    Langlands.SchemeModule.RigidifiedModule.pullbackCoherence S' ((baseChange b).obj A)
    _ _ (poincareFamilyBaseChange b A hA) (poincareFamily ((baseChange b).obj A) hA')
    (poincareFamilyBaseChange_universal universality b A hA)
    (poincareFamily_universal ((baseChange b).obj A) hA'))).1

/-- Every compatible parameter isomorphism is this canonical comparison. -/
lemma dualSchemeBaseChangeIso_unique
    (e : (Over.pullback b).obj (dualScheme A hA) ≅ dualScheme ((baseChange b).obj A) hA')
    (he : Nonempty ((RigidifiedLineBundle.relativePullback ((baseChange b).obj A).X.hom
      (unitSection ((baseChange b).obj A)) (unitSection_comp _) e.hom).obj
        (poincareFamily ((baseChange b).obj A) hA') ≅ poincareFamilyBaseChange b A hA)) :
    e = dualSchemeBaseChangeIso universality b A hA hA' :=
  (Classical.choose_spec (picardZeroUniversalUniqueness
    Langlands.SchemeModule.RigidifiedModule.pullbackCoherence S' ((baseChange b).obj A)
    _ _ (poincareFamilyBaseChange b A hA) (poincareFamily ((baseChange b).obj A) hA')
    (poincareFamilyBaseChange_universal universality b A hA)
    (poincareFamily_universal ((baseChange b).obj A) hA'))).2 e he

/-- The forward comparison is exactly the classifier of the actual pulled-back family. -/
lemma dualSchemeBaseChangeIso_hom :
    (dualSchemeBaseChangeIso universality b A hA hA').hom =
      dualClassify ((baseChange b).obj A) hA' _
        ⟨RigidifiedLineBundle.classOf ((baseChange b).obj A).X.hom
          (unitSection ((baseChange b).obj A)) (unitSection_comp _)
          (poincareFamilyBaseChange b A hA),
          (poincareFamilyBaseChange_universal universality b A hA).1⟩ :=
  dualClassify_unique ((baseChange b).obj A) hA' _ _ _
    (Quotient.sound ⟨dualSchemeBaseChangePullbackIso universality b A hA hA'⟩)

end Langlands.AbelianScheme
