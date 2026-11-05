import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicEvaluation
import Langlands.AlgebraicGeometry.ProjectiveBundle.Geometry
import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationImmersion
import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationPullback

/-! # The actual projective evaluation of the canonical cubic bundle -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.ProjectiveBundle

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n : ℕ}

/-- The projective dimension used by cubic linear rigidification. -/
def cubicProjectiveDimension (g d : ℕ) : ℕ := 6 ^ g * d - 1

lemma cubicProjectiveDimension_add_one (g d : ℕ) (hd : 0 < d) :
    cubicProjectiveDimension g d + 1 = 6 ^ g * d := by
  apply Nat.sub_add_cancel
  exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.pow_pos (by decide)) hd)

variable (a : Datum P S g d n) (hd : 0 < d)
    (hM : IsLocallyFreeOfRank a.rigidificationModule (6 ^ g * d))

include hd hM in
/-- Reindex the given actual direct-image rank by its projective dimension. -/
lemma Datum.cubicProjectiveRank :
    IsLocallyFreeOfRank a.rigidificationModule (cubicProjectiveDimension g d + 1) := by
  rw [cubicProjectiveDimension_add_one g d hd]
  exact hM

/-- The actual projectivization of the cubic direct image, constructed by its
local frames in dimension `6^g*d - 1`. -/
def Datum.cubicProjectiveBundle : Scheme.{u} :=
  frameBundle a.rigidificationModule (cubicProjectiveDimension g d)
    (a.cubicProjectiveRank hd hM)

/-- The structure map of the actual cubic projective bundle. -/
def Datum.cubicProjectiveProjection : a.cubicProjectiveBundle hd hM ⟶ S :=
  FrameBundle.toBase (a.cubicProjectiveRank hd hM)

/-- The actual degree-one line bundle on the cubic projective bundle. -/
def Datum.cubicProjectiveTwistOne : LineBundle (a.cubicProjectiveBundle hd hM) :=
  FrameBundle.twistOne (a.cubicProjectiveRank hd hM)

instance Datum.isProper_cubicProjectiveProjection :
    IsProper (a.cubicProjectiveProjection hd hM) :=
  FrameBundle.isProper_toBase (a.cubicProjectiveRank hd hM)

variable
    (hgen : EvaluationGenerates a.abelian.X.hom a.cubicBundle (𝟙 a.rigidificationModule))

/-- Evaluate the actual full cubic direct image into its actual projective bundle. -/
def Datum.cubicProjectiveEvaluation :
    a.abelian.X.left ⟶ a.cubicProjectiveBundle hd hM :=
  evaluationMap a.abelian.X.hom a.cubicBundle (𝟙 a.rigidificationModule)
    (a.cubicProjectiveRank hd hM)
    (hgen.frameEvaluationGenerates a.abelian.X.hom a.cubicBundle (𝟙 a.rigidificationModule))

/-- Cubic projective evaluation is a morphism over the original base. -/
@[reassoc (attr := simp)]
lemma Datum.cubicProjectiveEvaluation_toBase :
    a.cubicProjectiveEvaluation hd hM hgen ≫ a.cubicProjectiveProjection hd hM =
      a.abelian.X.hom :=
  evaluationMap_toBase a.abelian.X.hom a.cubicBundle (𝟙 a.rigidificationModule)
    (a.cubicProjectiveRank hd hM) _

/-- The actual cubic evaluation, as a morphism in the category over the base. -/
def Datum.cubicProjectiveEvaluationOver :
    a.abelian.X ⟶ Over.mk (a.cubicProjectiveProjection hd hM) :=
  Over.homMk (a.cubicProjectiveEvaluation hd hM hgen)
    (a.cubicProjectiveEvaluation_toBase hd hM hgen)

/-- The global degree-one bundle pulls back to the datum's actual cubic bundle. -/
def Datum.cubicProjectiveEvaluationPullbackIso :
    (LineBundle.pullback (a.cubicProjectiveEvaluation hd hM hgen)).obj
        (a.cubicProjectiveTwistOne hd hM) ≅ a.cubicBundle :=
  ObjectProperty.isoMk _
    (EvaluationPullback.globalIso a.abelian.X.hom a.cubicBundle (𝟙 a.rigidificationModule)
      (a.cubicProjectiveRank hd hM)
      (hgen.frameEvaluationGenerates a.abelian.X.hom a.cubicBundle (𝟙 a.rigidificationModule)))

/-- The constructed cubic evaluation is proper, using the properness already
contained in the actual abelian scheme. -/
instance Datum.isProper_cubicProjectiveEvaluation :
    IsProper (a.cubicProjectiveEvaluation hd hM hgen) := by
  dsimp only [Datum.cubicProjectiveEvaluation]
  infer_instance

/-- Cubic projective evaluation is a closed immersion precisely when its actual
local frame evaluations are closed immersions. -/
lemma Datum.isClosedImmersion_cubicProjectiveEvaluation_iff :
    IsClosedImmersion (a.cubicProjectiveEvaluation hd hM hgen) ↔
      ∀ U : FrameOpen a.rigidificationModule (cubicProjectiveDimension g d),
        IsClosedImmersion
          (localEvaluationMap a.abelian.X.hom a.cubicBundle (𝟙 a.rigidificationModule)
            (frame a.rigidificationModule (cubicProjectiveDimension g d) U) U.val le_rfl
            (hgen.frameEvaluationGenerates a.abelian.X.hom a.cubicBundle
              (𝟙 a.rigidificationModule) U)) :=
  isClosedImmersion_evaluationMap_iff a.abelian.X.hom a.cubicBundle
    (𝟙 a.rigidificationModule) (a.cubicProjectiveRank hd hM) _

end Langlands.AbelianScheme.PolarizedFiniteLevel
