import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! # Compactness of continuous cuspidal convolutions for adelic `GL_n` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

local notation "GLₙ(" F ", " n ")" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GLₙ(F, n)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance (F : Type u) [Field F] (n : ℕ) :
    Smooth (GLₙ(F, n)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- Every compactly supported continuous weight on the full adelic `GL_n` defines a
compact integrated right-translation operator on the full almost-everywhere
cuspidal Hilbert space, for the given positive-central quotient data. -/
def GeneralLinearFullAEL2CuspidalCompactnessStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ)
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive (GLₙ(F, n)))
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ GLₙ(F, n))
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F (GLₙ(F, n)))).IsMulRightInvariant],
    ∀ (f : C_c(AdelicGroupPoints F (GLₙ(F, n)), ℂ)) (hf : Integrable f Measure.haar),
      IsCompactOperator (fullAEL2CuspidalIntegratedAction F (GLₙ(F, n)) hPD hG T i hi I e hc
        Measure.haar f hf)

end Langlands.Automorphic.GroupSchemeFunctions
