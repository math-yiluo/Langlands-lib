import Langlands.AllFieldBZ.Group.GL.Padic
import Langlands.Representation.Derivative.Partial

/-!
# All-field port of `Langlands.Representation.Derivative.Partial`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.Partial` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding partialDerivative partialDerivativeMk partialDerivativeMk_surjective partialDerivativeMk_unipotent partialDerivative_action_mk partialDerivative_map_mk
universe uF uV uW uX

namespace Partial
open Langlands.Derivative.Partial
open Langlands.GeneralLinear
open Langlands.Jacquet.Localization hiding action action_mk isSmooth_action map map_comp map_id map_mk mk mk_eq_zero mk_surjective quotientMap relations smoothFunctor smoothObject
variable {F : Type uF} [CommRing F]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {X : Type uX} [AddCommGroup X] [Module ℂ X]

section Topology
variable [TopologicalSpace F]

end Topology
section Topology
variable [TopologicalSpace F]

end Topology
end Partial
variable {F : LocalFieldPackage.{uF}}

/-- Zelevinsky's actual partial derivative, in every pair of natural ranks. -/
def partialDerivative (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) :
    letI := T.topology
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear m F.Carrier) ⥤
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier) := by
  letI := T.topology
  exact Partial.smoothFunctor ψ.complex k m

/-- The actual quotient map into the object of the partial-derivative functor. -/
def partialDerivativeMk (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear m F.Carrier),
      A →ₗ[ℂ] (partialDerivative T ψ k m).obj A := by
  letI := T.topology
  intro A
  exact Partial.mk ψ.complex k m A.representation

theorem partialDerivativeMk_surjective (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear m F.Carrier),
      Function.Surjective (partialDerivativeMk T ψ k m A) := by
  let := T.topology
  intro A
  exact Partial.mk_surjective ψ.complex k m A.representation

theorem partialDerivativeMk_unipotent (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear m F.Carrier))
      (u : GeneralLinear.upperUnipotent m F.Carrier) (v : A),
      partialDerivativeMk T ψ k m A (A.representation (1, u.val) v) =
        (Whittaker.entrywiseCharacter ψ.complex m u : ℂ) • partialDerivativeMk T ψ k m A v := by
  let := T.topology
  intro A u v
  exact Partial.mk_unipotent ψ.complex k m A.representation u v

theorem partialDerivative_action_mk (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear m F.Carrier))
      (g : GeneralLinear k F.Carrier) (v : A),
      ((partialDerivative T ψ k m).obj A).representation g (partialDerivativeMk T ψ k m A v) =
        partialDerivativeMk T ψ k m A (A.representation (g, 1) v) := by
  intros
  rfl

theorem partialDerivative_map_mk (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear m F.Carrier)}
      (f : A ⟶ B) (v : A),
      SmoothRep.hom ((partialDerivative T ψ k m).map f) (partialDerivativeMk T ψ k m A v) =
        partialDerivativeMk T ψ k m B (SmoothRep.hom f v) := by
  intros
  rfl

end Langlands.AllFieldBZ.Derivative
