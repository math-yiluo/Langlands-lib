import Langlands.Automorphic.ArchimedeanPlaceParameter
import Langlands.LocalFactor.ArchimedeanGamma

/-! # An explicit real standard-module coefficient space -/

noncomputable section

open scoped Classical Manifold ContDiff Matrix.Norms.Operator
open Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

/-- The real matrix height, using both the matrix and its inverse. -/
def realMatrixHeight {n : ℕ} (g : Langlands.GeneralLinear n ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    (‖g.val i j‖ ^ 2 + ‖(g⁻¹).val i j‖ ^ 2)

/-- The standard unipotent character for the real additive parameter `a`. -/
def realWhittakerCharacter {r : ℕ} (a : ℝˣ)
    (u : Langlands.GeneralLinear (r + 1) ℝ) : ℂ :=
  (realScaledCharacter a).complex (∑ i : Fin r, u.val i.castSucc i.succ)

/-- A smooth, moderate-growth coefficient map of the actual standard `(g,K)` module.
Identification with a continuous induced-model coefficient space is a separate obligation. -/
def IsRealWhittakerIntertwiner (r : ℕ) (ds : List RealBlock) (a : ℝˣ)
    (B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ)) : Prop :=
  (∀ f : Automorphic.realStandardKFinite (r + 1) ds,
    ∀ u ∈ GeneralLinear.upperUnipotent (r + 1) ℝ,
    ∀ g : Langlands.GeneralLinear (r + 1) ℝ,
      B f (u * g) = realWhittakerCharacter a u * B f g) ∧
  (∀ f : Automorphic.realStandardKFinite (r + 1) ds,
    ContMDiff (Archimedean.matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ (B f)) ∧
  (∀ f : Automorphic.realStandardKFinite (r + 1) ds,
    ∃ (C : ℝ) (N : ℕ), ∀ g : Langlands.GeneralLinear (r + 1) ℝ,
      ‖B f g‖ ≤ C * realMatrixHeight g ^ N) ∧
  (∀ (k : Archimedean.unitaryCompact ℝ (r + 1))
    (f f' : Automorphic.realStandardKFinite (r + 1) ds),
    (f' : Langlands.GeneralLinear (r + 1) ℝ → ℂ) =
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (r + 1) ℝ)
          (k : Langlands.GeneralLinear (r + 1) ℝ) f →
      B f' = Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (r + 1) ℝ)
        (k : Langlands.GeneralLinear (r + 1) ℝ) (B f)) ∧
  ∀ (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
    (f f' : Automorphic.realStandardKFinite (r + 1) ds),
    (f' : Langlands.GeneralLinear (r + 1) ℝ → ℂ) =
        Archimedean.rightDerivative (Archimedean.matrixModel ℝ (r + 1)) X
          (f : Langlands.GeneralLinear (r + 1) ℝ → ℂ) →
      B f' = Archimedean.rightDerivative (Archimedean.matrixModel ℝ (r + 1)) X (B f)

/-- Span of the images of all specified real standard-module coefficient maps.
No equality with a Casselman–Wallach Whittaker space is asserted by this definition. -/
def realWhittakerModel (r : ℕ) (ds : List RealBlock) (a : ℝˣ) :
    Submodule ℂ (Langlands.GeneralLinear (r + 1) ℝ → ℂ) :=
  ⨆ (B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ))
    (_ : IsRealWhittakerIntertwiner r ds a B), LinearMap.range B

namespace RealLocalJacquet

/-- Dualize each explicit block using its actual inverse inducing character. -/
def dualBlock : RealBlock → RealBlock
  | .character c => .character c.inverse
  | .induced d => .induced d.inverse

theorem rank_dualBlock (d : RealBlock) : (dualBlock d).rank = d.rank := by
  cases d <;> rfl

theorem realRank_map_dualBlock (ds : List RealBlock) :
    realRank (ds.map dualBlock) = realRank ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.map_cons, realRank_cons, rank_dualBlock, ih]

end RealLocalJacquet
end Langlands.Global.RankinSelbergGlobal
