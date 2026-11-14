import Langlands.Representation.Parabolic.ComposedFunctors
import Langlands.AllField.Representation.Parabolic.RefinementCompositionSupplement
/-! Direct normalized functors for the actual composed matrix parabolic. -/

noncomputable section

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic
open Langlands.AllField.Parabolic

open Langlands.GeneralLinear
open Langlands.Geometric

universe uF uV uW


end Langlands.AllField.Parabolic

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open _root_.CategoryTheory
open Langlands.GeneralLinear hiding SupercuspidalClass
open Langlands.Geometric
open Langlands.Parabolic
open Langlands.AllField.Parabolic

universe uF uV uW

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Inflation through the actual composite projection, with the positive half. -/
abbrev composedInducingRepresentation
    (σ : Representation ℂ (refinedLevi F B S) V) :
    Representation ℂ (composedParabolic F B S) V :=
  twist (T.composedParabolicHalfModulus B S)
    (σ.comp (composedLeviProjection F B S))

/-- Direct smooth induction from the smaller actual matrix parabolic. -/
def normalizedComposedInduced (σ : Representation ℂ (refinedLevi F B S) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation ℂ (GeneralLinear n F)
      (Induction.SmoothFunctions (composedParabolic F B S)
        (T.composedInducingRepresentation B S σ)) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  exact Induction.smoothInduced _ _

/-- Inflate and twist an intertwiner using the composite projection. -/
def composedInducingMap
    {σ : Representation ℂ (refinedLevi F B S) V}
    {τ : Representation ℂ (refinedLevi F B S) W} (f : σ.IntertwiningMap τ) :
    (T.composedInducingRepresentation B S σ).IntertwiningMap
      (T.composedInducingRepresentation B S τ) :=
  twistIntertwining _
    { toLinearMap := f.toLinearMap
      isIntertwining' := fun q => f.isIntertwining' (composedLeviProjection F B S q) }

/-- The direct induced intertwiner acts by pointwise postcomposition. -/
def normalizedComposedInducedMap
    {σ : Representation ℂ (refinedLevi F B S) V}
    {τ : Representation ℂ (refinedLevi F B S) W} (f : σ.IntertwiningMap τ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedComposedInduced B S σ).IntertwiningMap
      (T.normalizedComposedInduced B S τ) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  exact Induction.smoothInducedMap _ (T.composedInducingMap B S f)

theorem isSmooth_normalizedComposedInduced
    (σ : Representation ℂ (refinedLevi F B S) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsSmooth (T.normalizedComposedInduced B S σ) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  exact Induction.smoothInduced_smooth _ _

/-- Direct normalized induction between the actual smooth categories. -/
def normalizedComposedInductionFunctor :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (refinedLevi F B S) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  exact {
    obj := fun A => SmoothRep.of (T.normalizedComposedInduced B S A.representation)
      (T.isSmooth_normalizedComposedInduced B S A.representation)
    map := fun f => SmoothRep.ofHom (T.normalizedComposedInducedMap B S (SmoothRep.hom f))
    map_id := by intros; ext φ x; rfl
    map_comp := by intros; ext φ x; rfl }

end Langlands.LocalFieldData
