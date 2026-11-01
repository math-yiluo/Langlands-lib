import Langlands.Representation.Derivative.Homogeneity
import Langlands.Representation.Mirabolic.MixedProducts

/-!
# Homogeneity of left mixed products

Zelevinsky's proposition that the left mixed product of an arbitrary
representation of `GL_k` with a homogeneous representation of a mirabolic
group is homogeneous. No proof is supplied.
-/

noncomputable section

namespace Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- For every representation `ρ` of `GL_k` and every homogeneous representation
`τ` of `P_(r+1)`, the actual left mixed product `ρ × τ` of `P_(k+r+1)` is
homogeneous. -/
def LeftMixedProductHomogeneity : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k r : ℕ) (ρ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
    (τ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear.mirabolic r F.Carrier)),
    IsHomogeneous T ψ τ →
      IsHomogeneous T ψ ((T.leftMixedProductFunctor k r).obj (ρ, τ))

end Langlands.Derivative
