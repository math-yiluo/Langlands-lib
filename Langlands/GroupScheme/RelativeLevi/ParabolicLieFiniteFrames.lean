import Langlands.GroupScheme.Lie.FiniteLocalFrames
import Langlands.GroupScheme.RelativeLevi.ParabolicPresheaf

/-! # Actual finite local Lie frames for relative parabolic families -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {P G : GroupScheme S} {j : P ⟶ G}

/-- A relative parabolic's actual Lie sheaf has finite local bases. -/
theorem IsRelativeParabolicSubgroup.lie_hasFiniteLocalBasis
    (hj : IsRelativeParabolicSubgroup j) :
    ∃ q : SheafOfModules.LocalGeneratorsData.{u} P.Lie,
      q.IsLocallyFreeData ∧ q.IsFiniteType :=
  P.lie_hasFiniteLocalBasis hj.smooth

namespace ParabolicSubgroupModuli.ParabolicRepresentative

variable {F : ParabolicSubgroupModuli.ParabolicSubgroup G}
    (r : ParabolicSubgroupModuli.ParabolicRepresentative F)

/-- Finite local frames concern the actual group of this representative. -/
theorem lie_hasFiniteLocalBasis :
    ∃ q : SheafOfModules.LocalGeneratorsData.{u} r.group.Lie,
      q.IsLocallyFreeData ∧ q.IsFiniteType :=
  r.parabolic.lie_hasFiniteLocalBasis

/-- The proved smooth-group frames of an actual parabolic representative. -/
abbrev lieFiniteLocalBasisData :
    SheafOfModules.LocalGeneratorsData.{u} r.group.Lie :=
  r.group.lieFiniteLocalBasisData r.parabolic.smooth

/-- Each chosen parabolic Lie chart is isomorphic to its finite free sheaf. -/
def lieFiniteLocalBasisTrivialization (i : r.lieFiniteLocalBasisData.I) :
    SheafOfModules.free (R := S.ringCatSheaf.over (r.lieFiniteLocalBasisData.X i))
        (r.lieFiniteLocalBasisData.generators i).I ≅
      r.group.Lie.over (r.lieFiniteLocalBasisData.X i) :=
  r.group.lieFiniteLocalBasisTrivialization r.parabolic.smooth i

end ParabolicSubgroupModuli.ParabolicRepresentative

end Langlands.GroupScheme
