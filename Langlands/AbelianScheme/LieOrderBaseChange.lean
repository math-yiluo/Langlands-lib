import Langlands.AbelianScheme.LieBaseChangeProof
import Langlands.AbelianScheme.LieDeterminant
import Langlands.AbelianScheme.RationalBaseChange

/-! # Actual order pullback and the canonical Lie comparison -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

namespace Langlands.AbelianScheme

variable {S T : AlgebraicGeometry.Scheme.{u}} (b : T ⟶ S)
    (B : AbelianScheme S)

/-- The ring map on actual integral endomorphisms induced by abelian-scheme pullback. -/
def baseChangeEnd : End B →+* End ((baseChange b).obj B) where
  toFun := (baseChange b).map
  map_zero' := (baseChange b).map_zero B B
  map_one' := (baseChange b).map_id B
  map_add' := fun _ _ => (baseChange b).map_add
  map_mul' := fun f g => (baseChange b).map_comp g f

@[simp]
theorem baseChangeEnd_apply (f : End B) :
    baseChangeEnd b B f = (baseChange b).map f := rfl

variable {O : Type v} [Ring O]

/-- Pull back the actual order action through the actual base-change functor. -/
def baseChangeOrderAction (α : O →+* End B) :
    O →+* End ((baseChange b).obj B) :=
  (baseChangeEnd b B).comp α

@[simp]
theorem baseChangeOrderAction_apply (α : O →+* End B) (a : O) :
    baseChangeOrderAction b B α a = (baseChange b).map (α a) := rfl

/-- The pulled-back order acts by the Lie maps of the pulled-back endomorphisms. -/
theorem lieOrderAction_baseChange (α : O →+* End B) (a : O) :
    lieOrderAction ((baseChange b).obj B) (baseChangeOrderAction b B α) a =
      lieMap ((baseChange b).map (α a)) := rfl

/-- Select only from the proved canonical Lie base-change existence theorem. -/
def lieBaseChangeIso :
    (AlgebraicGeometry.Scheme.Modules.pullback b).obj B.Lie ≅
      ((baseChange b).obj B).Lie :=
  ((lieBaseChange S) T b B).2.choose

/-- The selected comparison satisfies the actual cotangent/dual characterization. -/
theorem lieBaseChangeIso_characterization :
    (lieBaseChangeIso b B).hom ≫
        dualMap (GroupScheme.cotangentBaseChangeMap b B.toGrp) =
      dualPullbackComparison b (GroupScheme.cotangentAtIdentity B.toGrp) :=
  ((lieBaseChange S) T b B).2.choose_spec

/-- The canonical equation determines the comparison; there is no arbitrary model choice. -/
theorem lieBaseChangeIso_unique
    (ell : (AlgebraicGeometry.Scheme.Modules.pullback b).obj B.Lie ≅
      ((baseChange b).obj B).Lie)
    (hell : ell.hom ≫ dualMap (GroupScheme.cotangentBaseChangeMap b B.toGrp) =
      dualPullbackComparison b (GroupScheme.cotangentAtIdentity B.toGrp)) :
    ell = lieBaseChangeIso b B := by
  have : IsIso (GroupScheme.cotangentBaseChangeMap b B.toGrp) :=
    ((lieBaseChange S) T b B).1
  apply Iso.ext
  apply (cancel_mono (dualMap (GroupScheme.cotangentBaseChangeMap b B.toGrp))).mp
  rw [hell, lieBaseChangeIso_characterization]

end Langlands.AbelianScheme
