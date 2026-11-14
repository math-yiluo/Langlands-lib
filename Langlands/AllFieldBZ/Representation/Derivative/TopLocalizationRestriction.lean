import Langlands.AllFieldBZ.Representation.Derivative.PartialDerivativeTensorStatement
import Langlands.Representation.Derivative.TopLocalizationRestriction

/-!
# All-field port of `Langlands.Representation.Derivative.TopLocalizationRestriction`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.TopLocalizationRestriction` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative.TopLocalization
open Langlands.Derivative.TopLocalization hiding upperRestrictionIso
open Langlands.GeneralLinear
open Langlands.Jacquet.Localization
universe uF uV

variable {F : Type uF} [CommRing F] {n : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

section Smooth
variable [TopologicalSpace F]

end Smooth
section Padic
variable {K : LocalFieldPackage.{uF}}

/-- The actual `GL_(n+1)` and mirabolic full upper quotients are naturally
isomorphic, with identity maps on original representatives. -/
def upperRestrictionIso (T : K.TopologicalData) (ψ : AddChar K.Carrier ℂ) (n : ℕ) :
    letI := T.topology
    Langlands.Derivative.PartialTensor.upperCoinvariantsFunctor.{uF,uV} ψ (n + 1) ≅
      generalLinearRestriction T n ⋙ mirabolicUpperCoinvariantsFunctor ψ n := by
  letI := T.topology
  refine NatIso.ofComponents (fun A => SmoothRep.mkIso
    { toLinearEquiv := upperRestrictionLinearEquiv ψ A.representation
      isIntertwining' := fun _ => rfl }) ?_
  intro A B f
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply hom_ext
  ext v
  rfl

end Padic
end Langlands.AllFieldBZ.Derivative.TopLocalization
