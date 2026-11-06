import Langlands.Automorphic.GeneralLinearCuspidalComparison
import Langlands.Automorphic.GroupSchemeParabolicMeasure

/-! # All-proper and standard maximal-block GL cuspidality -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme

local instance comparisonGeneralLinearIsAffine
    (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance comparisonGeneralLinearSmooth
    (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- Equality on the original continuous function carrier of intrinsic normalized
all-proper-parabolic vanishing and the original standard maximal-block condition. -/
def GeneralLinearParabolicCuspidalComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ)
    (hPD : ParabolicDynamicStatement.{u})
    (hG : IsConnectedReductive
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))
    [CompactSpace (AdeleQuotient F)],
    normalizedParabolicCuspidalSubrepresentation F
        (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)) hPD hG =
      generalLinearStandardBlockVanishingSubrepresentation F n

end Langlands.Automorphic.GroupSchemeFunctions
