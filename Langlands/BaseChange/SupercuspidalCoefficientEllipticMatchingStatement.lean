import Langlands.BaseChange.CuspForm
import Langlands.BaseChange.TwistedCharacter
import Langlands.Representation.Classification.Supercuspidal
import Mathlib.RepresentationTheory.Irreducible

/-!
# Elliptic matching of supercuspidal matrix coefficients

The statement that, for a cyclic field extension `E/F` of nonarchimedean local fields of
characteristic zero with generator `σ`, an irreducible supercuspidal representation `τ` of
`GL_n(E)` with an isomorphism `A` of `τ` onto `τ^σ`, and an irreducible supercuspidal
representation `π` of `GL_n(F)` whose characters satisfy the identity
`Θ_τ^{A⁻¹}(δ⁻¹) = c Θ_π(γ⁻¹)` at every associated pair `(δ, γ)` with `γ` regular elliptic,
there are cusp forms `φ` on `GL_n(E)` and `f` on `GL_n(F)` (cut-off matrix coefficients of the
contragredients) that concord at every such pair, with `f` zero at the regular elliptic
elements that are not norms and `tr(τ(φ) ∘ A) ≠ 0`. This is the elliptic part of the matching
of cusp forms at an auxiliary place (Henniart–Lemaire 2011, II.4.10, Lemme 2, and II.6.3–II.6.4).
Statement only; not proved here. See the paired Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis

/-- For a nonarchimedean local field `F` of characteristic zero, a field `E` that is a cyclic
`F`-algebra of group `⟨σ⟩` of order `l` with its module topology, and `0 < n`: let `τ` be an
irreducible supercuspidal representation of `GL_n(E)` on `W : Type uW` with an isomorphism `A`
of `τ` onto `τ^σ`, and `π` an irreducible supercuspidal representation of `GL_n(F)` on
`V : Type uV`. Suppose `c ≠ 0` and, for every `δ ∈ GL_n(E)` associated with a regular elliptic
`γ ∈ GL_n(F)`, the character of `π` has a value `a` at `γ⁻¹` and the distribution
`φ ↦ tr(τ(φ) ∘ A⁻¹)` has the value `c * a` at `δ⁻¹`. Then for all Haar measures `μF` on
`GL_n(F)` and `μE` on `GL_n(E)` (Borel σ-algebras) there are Schwartz–Bruhat functions `φ` on
`GL_n(E)` and `f` on `GL_n(F)`, both with vanishing constant terms, such that `f` vanishes at
every regular elliptic element that is not a norm, `φ` and `f` concord (HL I.2.5) at every
associated pair `(δ, γ)` with `γ` regular elliptic, and `tr(τ(φ) ∘ A) ≠ 0`. -/
def SupercuspidalCoefficientEllipticMatchingStatement.{u, v, uV, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) → 0 < n →
    haveI : Module.Finite F E := hE.1
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : GeneralLinear.IsSupercuspidal τ),
      τ.IsIrreducible → ∀ (A : SigmaIntertwiner σ n τ)
      {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear n F) V) (hπ : GeneralLinear.IsSupercuspidal π),
      π.IsIrreducible → ∀ c : ℂ, c ≠ 0 →
      (∀ (δ : GeneralLinear n E) (γ : GeneralLinear n F), IsNormAssociated σ l δ γ →
        IsRegularElliptic γ → ∃ a : ℂ, HasCharacterValue π hπ.1 γ⁻¹ a ∧
          HasTwistedCharacterValue τ hτ.1 A.symm.toLinearMap δ⁻¹ (c * a)) →
      ∀ (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
        (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure],
        ∃ (φ : SchwartzBruhat (GeneralLinear n E)) (f : SchwartzBruhat (GeneralLinear n F)),
          HasVanishingConstantTerms (φ : GeneralLinear n E → ℂ) ∧
            HasVanishingConstantTerms (f : GeneralLinear n F → ℂ) ∧
            (∀ γ : GeneralLinear n F, IsRegularElliptic γ → ¬ IsNorm σ l γ →
              (f : GeneralLinear n F → ℂ) γ = 0) ∧
            (∀ (δ : GeneralLinear n E) (γ : GeneralLinear n F), IsNormAssociated σ l δ γ →
              IsRegularElliptic γ → ConcordAt σ l μF μE φ f δ γ) ∧
            twistedDistribution μE τ hτ.1 A.toLinearMap φ ≠ 0

end Langlands.BaseChange
