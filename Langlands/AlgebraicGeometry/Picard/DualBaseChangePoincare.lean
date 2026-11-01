import Langlands.AlgebraicGeometry.Picard.AmpleMumfordBaseChange
import Langlands.AlgebraicGeometry.Picard.FamilyBaseChangeNaturality

/-! # Poincare pullbacks along base-changed dual maps -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

variable {S S' : Scheme.{u}} (b : S' ⟶ S)

/-- The mate of a pulled-back parameter map is the projection followed by that map. -/
lemma baseChangeParameterMate_pullback_map {Q P : Over S} (g : Q ⟶ P) :
    baseChangeParameterMate b ((Over.pullback b).map g) = baseChangeParameterMap b Q ≫ g := by
  ext
  simp [baseChangeParameterMate, baseChangeParameterMap]

variable (universality : PicardZeroUniversalBaseChangeStatement.{u})
variable (A : AbelianScheme S) (hA : HasDualScheme A)

/-- The rigidified Poincare pullback along a pulled-back map followed by the canonical dual
comparison is the base change of the original rigidified Poincare pullback. -/
def dualSchemeBaseChangeIsoPullbackIso {Q : Over S} (f : Q ⟶ dualScheme A hA) :
    (RigidifiedLineBundle.relativePullback ((baseChange b).obj A).X.hom
      (unitSection ((baseChange b).obj A)) (unitSection_comp _)
      ((Over.pullback b).map f ≫ (dualSchemeBaseChangeIso universality b A hA
          (hasDualScheme_baseChange universality b A hA)).hom)).obj
        (poincareFamily ((baseChange b).obj A) (hasDualScheme_baseChange universality b A hA)) ≅
      (baseChangeFamily b A Q).obj
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
          f).obj (poincareFamily A hA)) :=
  ((RigidifiedLineBundle.relativePullbackComp RigidifiedModule.pullbackCoherence _ _ _
      ((Over.pullback b).map f) _).app _).symm ≪≫
    (RigidifiedLineBundle.relativePullback _ _ _ ((Over.pullback b).map f)).mapIso
      (dualSchemeBaseChangePullbackIso universality b A hA _) ≪≫
    (baseChangeFamilyPullbackIso b A ((Over.pullback b).map f)).app (poincareFamily A hA) ≪≫
    (familyBaseChange b A ((Over.pullback b).obj Q)).mapIso
      (eqToIso (by rw [baseChangeParameterMate_pullback_map]) ≪≫
        ((RigidifiedLineBundle.relativePullbackComp RigidifiedModule.pullbackCoherence _ _ _
          (baseChangeParameterMap b Q) f).app _).symm)

/-- After forgetting rigidifications, the Poincare pullback along a base-changed dual map is
the pullback of the original Poincare pullback along the actual total-space map. -/
def dualBaseChangeMapPoincareForgetIso (f : A.X ⟶ dualScheme A hA) :
    (RigidifiedLineBundle.forget (mumfordSection ((baseChange b).obj A))).obj
        ((RigidifiedLineBundle.relativePullback ((baseChange b).obj A).X.hom
          (unitSection ((baseChange b).obj A)) (unitSection_comp _)
          (dualBaseChangeMap A hA universality b f)).obj
            (poincareFamily ((baseChange b).obj A)
              (hasDualScheme_baseChange universality b A hA))) ≅
      (LineBundle.pullback (baseChangeFamilySpaceMap b A A.X)).obj
        ((RigidifiedLineBundle.forget (mumfordSection A)).obj
          ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
            f).obj (poincareFamily A hA))) :=
  (RigidifiedLineBundle.forget _).mapIso
      (dualSchemeBaseChangeIsoPullbackIso b universality A hA f) ≪≫
    (baseChangeFamilyForgetIso b A A.X).app _

end Langlands.AbelianScheme
