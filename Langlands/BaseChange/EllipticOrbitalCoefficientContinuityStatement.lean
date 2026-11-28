import Langlands.BaseChange.CentralQuotientFormalDegree
import Langlands.JacquetLanglands.LocalCharacter
import Langlands.JacquetLanglands.RegularElliptic

/-! # Local boundedness and continuity of elliptic orbital integrals of coefficients -/

open Filter Topology

namespace Langlands.BaseChange

open JacquetLanglands MeasureTheory

/-- Harish-Chandra's convergence and continuity of elliptic orbital integrals, for the matrix
coefficients of an irreducible representation of `GL_n(F)` that is square-integrable modulo the
center `Z`, as used in Clozel's proof of Proposition 5 (ii) (1991, §3). Let `μ` be a Haar
measure on `GL_n(F) / Z`, `γ` a regular elliptic element, `v` a vector and `ℓ` a smooth
functional. For `x ∈ GL_n(F)` let `o x` be the function `gZ ↦ ℓ(π(g x g⁻¹) v)` on
`GL_n(F) / Z`. On some open neighbourhood `U` of `γ` every `o x` is `μ`-integrable with
`∫ |o x| dμ` bounded uniformly in `x ∈ U`, and the orbital integral `x ↦ ∫ o x dμ` is
continuous at `γ`. -/
def EllipticOrbitalCoefficientContinuityStatement.{u, uV} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] (n : ℕ), 0 < n →
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    let G := GeneralLinear n F
    let Z := Subgroup.center G
    letI := centralQuotientMeasurableSpace F n
    ∀ (μ : Measure (G ⧸ Z)) [μ.IsHaarMeasure]
      {W : Type uV} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ G W), IsSquareIntegrable π → π.IsIrreducible →
      ∀ γ : G, IsRegularElliptic γ →
      ∀ (v : W) (ℓ : SmoothDual π), ∃ o : G → G ⧸ Z → ℂ,
        (∀ x g : G, o x (QuotientGroup.mk g) = ℓ.val (π (g * x * g⁻¹) v)) ∧
        ∃ U : Set G, IsOpen U ∧ γ ∈ U ∧ ∃ B : ℝ,
          (∀ x ∈ U, Integrable (o x) μ ∧ ∫ q, ‖o x q‖ ∂μ ≤ B) ∧
          Tendsto (fun x => ∫ q, o x q ∂μ) (𝓝 γ) (𝓝 (∫ q, o γ q ∂μ))

end Langlands.BaseChange
