import Langlands.GroupScheme.Reductive.SimplyConnectedPinnedModel
import Langlands.GroupScheme.Reductive.SimplyConnectedCorootSubtori
import Langlands.GroupScheme.Reductive.SimplyConnectedCentralizerDerived

/-! # Actual component-indexed derived centralizers of a pinned model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffineSimplyConnectedPinnedModel

open Langlands.LinearAlgebra.SimplyConnectedCartanComponents

variable (M : AffineSimplyConnectedPinnedModel.{u})

local instance : CommRing M.ring := M.toAffinePinnedModel.commRing
local instance : Fintype M.coordinates := M.toAffinePinnedModel.fintypeCoordinates
local instance : Fintype M.rootIndex := M.toAffinePinnedModel.fintypeRoots

/-- Components of the full constant based Cartan diagram of the model. -/
abbrev Component :=
  Langlands.LinearAlgebra.SimplyConnectedCartanComponents.Component M.basis

instance : Finite M.Component := inferInstance

/-- Simple indices outside a specified Cartan component. -/
abbrev Complement (c : M.Component) := {i : M.basis.support // component M.basis i ≠ c}

/-- The coordinate split torus spanned by the complementary simple coroots. -/
abbrev complementTorus (c : M.Component) : CommGroupScheme M.toAffinePinnedModel.base :=
  splitTorus.commGroupScheme M.toAffinePinnedModel.base (M.Complement c)

/-- The actual complementary subtorus map into the original coordinate torus. -/
def complementInclusion (c : M.Component) :
    (M.complementTorus c).toGrp ⟶
      splitTorus M.toAffinePinnedModel.base M.coordinates :=
  CommGroupScheme.groupHom
    (SimplyConnectedCorootSubtori.inclusion M.rootDatum M.basis M.corootSpan_eq_top
      {i | component M.basis i ≠ c} M.toAffinePinnedModel.base)

/-- The complementary torus is closed in the full coordinate torus. -/
theorem complementInclusion_closed (c : M.Component) :
    IsClosedSubgroup (M.complementInclusion c) :=
  SimplyConnectedCorootSubtori.inclusion_closed M.rootDatum M.basis M.corootSpan_eq_top
    {i | component M.basis i ≠ c} M.toAffinePinnedModel.base

/-- The complementary split torus as a subgroup of the original group. -/
def complementAmbient (c : M.Component) : (M.complementTorus c).toGrp ⟶ M.group :=
  M.complementInclusion c ≫ M.inclusion

/-- The complementary torus is closed in the original group. -/
theorem complementAmbient_closed (c : M.Component) :
    IsClosedSubgroup (M.complementAmbient c) :=
  (M.complementInclusion_closed c).comp M.closed

/-- Actual centralizer and relative derived data of the complementary torus. -/
def componentCentralizer (c : M.Component) :
    SplitTorusCentralizerDerivedModel (M.complementAmbient c) :=
  splitTorusCentralizerDerivedModel M.group M.reductive M.isFibrewiseSimplyConnected
    (M.complementTorus c) (M.complementAmbient c)
    (isSplitTorus_splitTorus (M.Complement c)) (M.complementAmbient_closed c)

/-- The actual component-indexed candidate factor. -/
abbrev componentGroup (c : M.Component) : GroupScheme M.toAffinePinnedModel.base :=
  (M.componentCentralizer c).derivedGroup

/-- Its actual closed inclusion in the original group. -/
def componentInclusion (c : M.Component) : M.componentGroup c ⟶ M.group :=
  (M.componentCentralizer c).ambientInclusion

/-- The candidate factor is reductive over the original affine base. -/
theorem componentGroup_isReductive (c : M.Component) :
    IsReductive (M.componentGroup c) := (M.componentCentralizer c).isReductive

/-- Its geometric fibres are simply connected. -/
theorem componentGroup_isFibrewiseSimplyConnected (c : M.Component) :
    IsFibrewiseSimplyConnected (M.componentGroup c) :=
  (M.componentCentralizer c).simplyConnected

/-- The candidate factor is closed in the original group. -/
theorem componentInclusion_closed (c : M.Component) :
    IsClosedSubgroup (M.componentInclusion c) :=
  (M.componentCentralizer c).ambientInclusion_closed

/-- The full coordinate torus factors through each complementary centralizer. -/
def centralizerTorusInclusion (c : M.Component) :
    splitTorus M.toAffinePinnedModel.base M.coordinates ⟶
      (M.componentCentralizer c).centralizer :=
  (M.componentCentralizer c).represents.factorHom M.inclusion
    (range_le_torusCentralizer_of_factor
      (A := M.complementTorus c)
      (B := splitTorus.commGroupScheme M.toAffinePinnedModel.base M.coordinates)
      (M.complementAmbient c) M.inclusion (M.complementInclusion c) rfl)

/-- The factored torus map has exactly the original ambient inclusion. -/
theorem centralizerTorusInclusion_comp (c : M.Component) :
    M.centralizerTorusInclusion c ≫ (M.componentCentralizer c).inclusion = M.inclusion :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- The full torus is closed in each complementary centralizer. -/
theorem centralizerTorusInclusion_closed (c : M.Component) :
    IsClosedSubgroup (M.centralizerTorusInclusion c) :=
  IsClosedSubgroup.of_comp (M.componentCentralizer c).closed
    (by rw [M.centralizerTorusInclusion_comp]; exact M.closed)

/-- It is maximal on every residue-field fibre of that centralizer. -/
theorem centralizerTorusInclusion_fibrewiseMaximal (c : M.Component) :
    IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme M.toAffinePinnedModel.base M.coordinates)
      (M.centralizerTorusInclusion c) := by
  intro s
  apply IsMaximalTorus.of_comp ((M.componentCentralizer c).closed.baseChange _)
  rw [← Functor.map_comp, M.centralizerTorusInclusion_comp]
  exact M.maximal s

end Langlands.GroupScheme.AffineSimplyConnectedPinnedModel
