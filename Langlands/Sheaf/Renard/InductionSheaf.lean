import Langlands.Sheaf.Renard.CompactInductionTestModule
import Langlands.Sheaf.Renard.SmoothProjectorActionSheaf

/-!
# Renard's induction sheaf on the original inverse-right homogeneous space

The original compact-induced test module is reconstructed by the actual
smooth projector-action-sheaf functor.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.InductionSheaf

open CategoryTheory
open Langlands.Induction
open Langlands.Sheaf.Equivariant
open Langlands.Sheaf.Renard.SectionActions
open Langlands.Sheaf.Renard.HomogeneousSections
open Langlands.Sheaf.Renard.CompatibleTestActions

attribute [local instance] homogeneousAction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (hG : Langlands.Topology.IsLocallyProfinite G)
variable (H : Subgroup G) (hH : IsClosed (H : Set G))

/-- The entire original compact-induced compatible action is smooth. -/
theorem compactCompatible_smooth (A : Rep.{0} ℂ H) :
    letI := hG.locallyCompactSpace
    CompactSectionActions.smoothProperty
      ((CompactInductionTestModule.functor G H hH).obj A) := by
  let := hG.locallyCompactSpace
  exact compactInduced_smooth H A.ρ

/-- The original compact-induction test-module functor, with smoothness retained. -/
def compatibleInduction :
    Rep.{0} ℂ H ⥤
      CompactSectionActions.SmoothCompatibleTestAction (G := G) (X := LeftQuotient H) :=
  letI := hG.locallyCompactSpace
  (CompactSectionActions.smoothProperty (G := G) (X := LeftQuotient H)).lift
    (CompactInductionTestModule.functor G H hH)
    (compactCompatible_smooth hG H hH)

/-- Renard III.3.2: the actual induction sheaf of a smooth H-representation. -/
def functor :
    Langlands.SmoothRep.{0, 0, 0} ℂ H ⥤ SmoothActionSheaf G (LeftQuotient H) :=
  Langlands.SmoothRep.toRep ⋙ compatibleInduction hG H hH ⋙
    SmoothProjectorActionSheaf.smoothFunctor (quotient_isLocallyProfinite H hG hH) hG

/-- The underlying action-sheaf functor uses the original compact-induced modules and maps. -/
def toActionIso :
    functor hG H hH ⋙ smoothActionInclusion G (LeftQuotient H) ≅
      (letI := hG.locallyCompactSpace
       Langlands.SmoothRep.toRep ⋙ CompactInductionTestModule.functor G H hH ⋙
         ProjectorActionSheaf.functor (quotient_isLocallyProfinite H hG hH)) :=
  Iso.refl _

/-- The ordinary sheaf is exactly the published projector sheaf of compact induction. -/
def underlyingSheafIso (A : Langlands.SmoothRep.{0, 0, 0} ℂ H) :
    underlying ((functor hG H hH).obj A).obj ≅
      (letI := hG.locallyCompactSpace
       ProjectorVectorSheaf.sheaf (quotient_isLocallyProfinite H hG hH)
         (CompactInductionTestModule.moduleObject H hH A.representation).property) :=
  letI := hG.locallyCompactSpace
  ProjectorActionSheaf.underlyingSheafIso (quotient_isLocallyProfinite H hG hH)
    (CompactInductionTestModule.compatibleObject H hH A.representation)

end Langlands.Sheaf.Renard.InductionSheaf
