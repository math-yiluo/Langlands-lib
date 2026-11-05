import Langlands.Global.AdelicGroupLocalPoints
import Langlands.GroupScheme.CocharacterTransport
import Langlands.GroupScheme.AffinePointBaseChangeSmooth
import Langlands.GroupScheme.Rational.PointTopology

/-! # Actual finite-completion points and rational points of the base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Global.FinitePlaceGroupPoints

open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The actual group scheme after extension to the given finite completion. -/
abbrev baseChangedGroup (v : FinitePlace F) :=
  (GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v))).obj G

/-- The existing pullback point comparison on the actual finite-completion carrier. -/
def baseChangeMulEquiv (v : FinitePlace F) :
    rationalPoints (baseChangedGroup F G v) ≃* FinitePlaceGroupPoints F G v :=
  baseChangeBasePointsEquiv (Spec.algebraMap F (FiniteCompletion F v)) G

/-- The point comparison is projection from the actual scheme pullback. -/
@[simp] theorem baseChangeMulEquiv_left (v : FinitePlace F)
    (x : rationalPoints (baseChangedGroup F G v)) :
    (baseChangeMulEquiv F G v x).left =
      x.left ≫ pullback.fst G.X.hom (Spec.algebraMap F (FiniteCompletion F v)) :=
  baseChangeBasePointsEquiv_left _ G x

/-- Postcomposition by an actual group-scheme morphism commutes with the comparison. -/
theorem baseChangeMulEquiv_map
    {P : GroupScheme (Spec (CommRingCat.of F))} (p : P ⟶ G) (v : FinitePlace F)
    (x : rationalPoints (baseChangedGroup F P v)) :
    baseChangeMulEquiv F G v
        (rationalPoints.map
          ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v))).map p) x) =
      P.affinePointsTarget p (CommAlgCat.of F (FiniteCompletion F v))
        (baseChangeMulEquiv F P v x) := by
  apply Over.OverMorphism.ext
  simp only [baseChangeMulEquiv_left, affinePointsTarget_apply, Over.comp_left]
  change (x.left ≫
      ((Over.pullback (Spec.algebraMap F (FiniteCompletion F v))).map p.hom.hom).left) ≫
      pullback.fst G.X.hom (Spec.algebraMap F (FiniteCompletion F v)) =
    (x.left ≫ pullback.fst P.X.hom (Spec.algebraMap F (FiniteCompletion F v))) ≫
      p.hom.hom.left
  simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst]

variable [IsAffine G.X.left]

local instance baseChanged_isAffine (v : FinitePlace F) :
    IsAffine (baseChangedGroup F G v).X.left := by
  change IsAffine (pullback G.X.hom (Spec.algebraMap F (FiniteCompletion F v)))
  infer_instance

local instance rationalPointTopologicalSpace (v : FinitePlace F) :
    TopologicalSpace (rationalPoints (baseChangedGroup F G v)) :=
  rationalPointTopology (FiniteCompletion F v) (baseChangedGroup F G v).X

local instance baseChangedAffineTopology (v : FinitePlace F) :
    TopologicalSpace
      ((baseChangedGroup F G v).affinePoints
        (CommAlgCat.of (FiniteCompletion F v) (FiniteCompletion F v))) :=
  (baseChangedGroup F G v).affinePointsTopologicalSpace _

/-- The same point comparison is a homeomorphism for the two original evaluation topologies. -/
theorem isHomeomorph_baseChangeMulEquiv (v : FinitePlace F) :
    IsHomeomorph (baseChangeMulEquiv F G v) := by
  let h : rationalPoints (baseChangedGroup F G v) ≃ₜ FinitePlaceGroupPoints F G v :=
    (rationalPointsAffineHomeomorph (baseChangedGroup F G v)).trans
      (affinePointsBaseChangeContinuousMulEquiv F (FiniteCompletion F v)
        (FiniteCompletion F v) G).symm.toHomeomorph
  have he : (baseChangeMulEquiv F G v :
      rationalPoints (baseChangedGroup F G v) → FinitePlaceGroupPoints F G v) = h := by
    funext x
    apply Over.OverMorphism.ext
    rw [baseChangeMulEquiv_left]
    change _ =
      ((affinePointsBaseChangeMulEquiv F (FiniteCompletion F v)
        (FiniteCompletion F v) G).symm
          (rationalPointsAffineHomeomorph (baseChangedGroup F G v) x)).left
    rw [affinePointsBaseChangeMulEquiv_symm_left, rationalPointsAffineHomeomorph_left]
  rw [he]
  exact h.isHomeomorph

/-- Actual finite-completion points and rational points of the actual base change
are continuously and multiplicatively equivalent. The source has the named
`rationalPointTopology`, bound only locally in this module. -/
def baseChangeContinuousMulEquiv (v : FinitePlace F) :
    rationalPoints (baseChangedGroup F G v) ≃ₜ* FinitePlaceGroupPoints F G v where
  toMulEquiv := baseChangeMulEquiv F G v
  continuous_toFun := (isHomeomorph_baseChangeMulEquiv F G v).continuous
  continuous_invFun :=
    ((baseChangeMulEquiv F G v).toEquiv.isHomeomorph_iff.mp
      (isHomeomorph_baseChangeMulEquiv F G v)).2

@[simp] theorem baseChangeContinuousMulEquiv_apply (v : FinitePlace F)
    (x : rationalPoints (baseChangedGroup F G v)) :
    baseChangeContinuousMulEquiv F G v x = baseChangeMulEquiv F G v x := rfl

end Langlands.Global.FinitePlaceGroupPoints
