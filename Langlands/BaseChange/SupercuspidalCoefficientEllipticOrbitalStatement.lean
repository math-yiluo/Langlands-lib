import Langlands.BaseChange.DeterminantWindow
import Langlands.BaseChange.TwistedCharacter
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.RepresentationTheory.Irreducible

/-!
# Twisted elliptic orbital integrals of cut-off supercuspidal coefficients

The statement that, for a cyclic field extension `E/F` of nonarchimedean local fields of
characteristic zero with generator `σ`, an irreducible supercuspidal representation `τ` of
`GL_n(E)` with an isomorphism `A` of `τ` onto `τ^σ`, a vector `v` and a smooth linear form
`λ`, and an element `δ` whose norm is associated with a regular elliptic element of `GL_n(F)`,
the σ-orbital integral of the coefficient `x ↦ λ(τ(x)⁻¹ v)` at `δ`, taken over `GL_n(E)` against
the determinant window normalized over the scalars `F^×`, is the value at `δ⁻¹` of the twisted
character of `A⁻¹` times the twisted trace `tr(τ(φ) ∘ A)` of the cut-off coefficient `φ`.
Statement only; not proved here. See the paired Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis

/-- For a nonarchimedean local field `F` of characteristic zero, a field `E` that is a cyclic
`F`-algebra of group `⟨σ⟩` of order `l` with its module topology, and `0 < n`, write
`b = determinantWindow F (n * l)` on `GL_n(E)` (the indicator of `0 ≤ ord_F N_{E/F}(det x) < nl`).
Let `τ` be an irreducible supercuspidal representation of `GL_n(E)` on `W : Type uW`, `A` an
isomorphism of `τ` onto `τ^σ`, `μE` a Haar measure on `GL_n(E)` (Borel σ-algebra), `v ∈ W`, `λ`
a smooth linear form, and `φ` the Schwartz–Bruhat function `x ↦ b(x) λ(τ(x)⁻¹ v)`. For every
`δ ∈ GL_n(E)` associated with a regular elliptic `γ ∈ GL_n(F)` and every value `Θ` at `δ⁻¹` of
the distribution `f ↦ tr(τ(f) ∘ A⁻¹)`, the function `x ↦ b(x) λ(τ(x⁻¹ δ x^σ)⁻¹ v)` has compact
support and its `μE`-integral is `Θ · tr(τ(φ) ∘ A)`. -/
def SupercuspidalCoefficientEllipticOrbitalStatement.{u, v, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) → 0 < n →
    haveI : Module.Finite F E := hE.1
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : GeneralLinear.IsSupercuspidal τ),
      τ.IsIrreducible → ∀ (A : SigmaIntertwiner σ n τ)
      (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure] (v : W) (ℓ : SmoothDual τ)
      (φ : SchwartzBruhat (GeneralLinear n E)),
      (∀ x : GeneralLinear n E,
        φ x = determinantWindow F (n * l) x * (ℓ : Module.Dual ℂ W) (τ x⁻¹ v)) →
      ∀ (δ : GeneralLinear n E) (γ : GeneralLinear n F), IsNormAssociated σ l δ γ →
        IsRegularElliptic γ → ∀ Θ : ℂ,
        HasTwistedCharacterValue τ hτ.1 A.symm.toLinearMap δ⁻¹ Θ →
        HasCompactSupport (fun x : GeneralLinear n E => determinantWindow F (n * l) x *
          (ℓ : Module.Dual ℂ W) (τ (x⁻¹ * δ * entrywiseAut σ n x)⁻¹ v)) ∧
        ∫ x, determinantWindow F (n * l) x *
            (ℓ : Module.Dual ℂ W) (τ (x⁻¹ * δ * entrywiseAut σ n x)⁻¹ v) ∂μE =
          Θ * twistedDistribution μE τ hτ.1 A.toLinearMap φ

end Langlands.BaseChange
