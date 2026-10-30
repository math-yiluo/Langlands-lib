import Langlands.AbelianScheme.Tate.WeilAlongHom0
import Langlands.AbelianScheme.Tate.WeilRationalFunctorialityStatement

/-! # Actual rational dual pullback and the Weil similitude equation -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A B : AbelianScheme S}
  (hA : HasDualScheme A) (hB : HasDualScheme B)
  (geometryA : DualSchemeGeometry A hA) (geometryB : DualSchemeGeometry B hB)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (additivity : DualSchemeMapAdditivity preservation stability A B hA hB)

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "DB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
local notation "dual0" => dualHom0 preservation composition unitCoherence associativity
  comparison symmetry stability hA hB additivity MA evaluationA MB evaluationB geometryA geometryB

/-- Pull back an actual rational dual-valued homomorphism by the actual rational
homomorphism and its constructed contravariant dual. -/
def rationalDualPullbackHom0 (f : Hom0 A B) (lamB : Hom0 B DB) : Hom0 A DA :=
  comp0 A DB DA (comp0 A B DB f lamB) (dual0 f)

local notation "pullback0" => rationalDualPullbackHom0 preservation composition unitCoherence
  associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA
  MB evaluationB additivity

/-- The geometric rational-Hom equation expressing a rational multiplier.
No pairing-preservation equation is supplied as replacement data. -/
def IsRationalDualPullbackMultiple (q : ℚ) (f : Hom0 A B)
    (lamA : Hom0 A DA) (lamB : Hom0 B DB) : Prop :=
  pullback0 f lamB = q • lamA

variable (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (functoriality : RationalWeilFunctorialityStatement.{u}) (T : Over S) (P : ℕ → Prop)

local notation "alongA" => rationalWeilAlongHom0BilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility T
local notation "alongB" => rationalWeilAlongHom0BilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hB geometryB MB evaluationB
  compatibility T
local notation "EA" => rationalWeilBilinearMap preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA compatibility T

include functoriality

/-- The pullback of the actual rational pairing agrees with the pairing of the
geometrically pulled-back dual-valued homomorphism. -/
lemma rationalWeilAlongHom0BilinearMap_pullback (f : Hom0 A B) (lamB : Hom0 B DB)
    (x y : Tate.Rational A T P) :
    alongB lamB P (Tate.rationalHomMap T P f x) (Tate.rationalHomMap T P f y) =
      alongA (pullback0 f lamB) P x y := by
  calc
    _ = EA P x (Tate.rationalHomMap T P (dual0 f)
        (Tate.rationalHomMap T P lamB (Tate.rationalHomMap T P f y))) :=
      functoriality preservation composition unitCoherence associativity comparison symmetry
        stability compatibility S A B hA hB geometryA geometryB MA evaluationA MB evaluationB
        additivity T P f x (Tate.rationalHomMap T P lamB (Tate.rationalHomMap T P f y))
    _ = _ := by
      change EA P x (Tate.rationalHomMap T P (dual0 f)
          (Tate.rationalHomMap T P lamB (Tate.rationalHomMap T P f y))) =
        EA P x (Tate.rationalHomMap T P
          (Rationalization.comp A DB DA
            (Rationalization.comp A B DB f lamB) (dual0 f)) y)
      rw [Tate.rationalHomMap_comp, Tate.rationalHomMap_comp]
      rfl

/-- A geometric rational-Hom multiplier implies the actual twist-valued
pairing multiplier, using the explicit rational functoriality proposition. -/
lemma rationalWeilAlongHom0BilinearMap_similitude (q : ℚ) (f : Hom0 A B)
    (lamA : Hom0 A DA) (lamB : Hom0 B DB)
    (hf : IsRationalDualPullbackMultiple preservation composition unitCoherence associativity
      comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB
      additivity q f lamA lamB) (x y : Tate.Rational A T P) :
    alongB lamB P (Tate.rationalHomMap T P f x) (Tate.rationalHomMap T P f y) =
      q • alongA lamA P x y := by
  rw [rationalWeilAlongHom0BilinearMap_pullback preservation composition unitCoherence
    associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA
    MB evaluationB additivity compatibility functoriality T P f lamB x y]
  change pullback0 f lamB = q • lamA at hf
  rw [hf]
  exact rationalWeilAlongHom0BilinearMap_smul preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility T
    q lamA P x y

end Langlands.AbelianScheme
