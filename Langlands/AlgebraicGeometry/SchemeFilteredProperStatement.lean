import Langlands.AlgebraicGeometry.SchemeFilteredRelativePropertyStatement
import Langlands.AlgebraicGeometry.SchemeFilteredPropertyStatement
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Properness along actual filtered ring and affine scheme limits -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

open AffineLimit

/-- A proper finitely presented scheme has a proper finitely presented model
at an actual original stage. -/
def SchemeFilteredProperModelExistence : Prop :=
  SchemeFilteredPropertyModelExistence.{u} @IsProper

/-- A prescribed finitely presented model is proper at the colimit exactly
when it is proper after an actual original ring transition. -/
def InitialRingModelProperDescent : Prop :=
  InitialRingModelPropertyDescent.{u} @IsProper

/-- Relative properness is detected at an actual affine-scheme limit stage. -/
def RelativeProperDescent : Prop :=
  RelativePropertyDescent.{u} @IsProper

/-- Relative properness along actual algebra spectra. -/
def SpectrumProperDescent : Prop :=
  SpectrumRelativePropertyDescent.{u} @IsProper

/-- Relative properness along actual outgoing original-ring transitions. -/
def InitialRingProperDescent : Prop :=
  InitialRingRelativePropertyDescent.{u} @IsProper

/-- The properness clause for arbitrary finitely presented source models. -/
def FinitePresentationInitialRingProperDescent : Prop :=
  FinitePresentationInitialRingRelativePropertyDescent.{u} @IsProper

/-- Proper model existence and all prescribed-model and relative forms. -/
def ProperDescent : Prop :=
  SchemeFilteredProperModelExistence.{u} ∧ InitialRingModelProperDescent.{u} ∧
    RelativeProperDescent.{u} ∧ SpectrumProperDescent.{u} ∧
    InitialRingProperDescent.{u} ∧ FinitePresentationInitialRingProperDescent.{u}

end Langlands.AlgebraicGeometry.SchemeLimitModel
