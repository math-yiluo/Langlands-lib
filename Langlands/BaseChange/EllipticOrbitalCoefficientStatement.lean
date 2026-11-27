import Langlands.BaseChange.CentralQuotientFormalDegree
import Langlands.JacquetLanglands.LocalCharacter
import Langlands.JacquetLanglands.RegularElliptic

/-! # Elliptic orbital integrals of square-integrable coefficients of `GL_n` -/

namespace Langlands.BaseChange

open JacquetLanglands MeasureTheory

/-- Clozel's Proposition 5 (ii) for `GL_n(F)`. Let `π` be an irreducible representation that is
square-integrable modulo the center `Z`, with formal degree `d` for a Haar measure `μ` on
`GL_n(F) / Z`, and let `γ` be a regular elliptic element at which the character of `π` has the
value `c`. For every vector `v` and smooth functional `ℓ`, the orbital integral
`∫_{G/Z} ℓ(π(g γ g⁻¹) v) dμ(gZ)` of the matrix coefficient converges absolutely and equals
`d⁻¹ ℓ(v) c`. -/
def EllipticOrbitalCoefficientStatement.{u, uV} : Prop :=
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
      (π : Representation ℂ G W) (hπ : IsSquareIntegrable π), π.IsIrreducible →
      ∀ d : ℝ, IsCentralFormalDegree μ π d →
      ∀ γ : G, IsRegularElliptic γ →
      ∀ c : ℂ, HasCharacterValue π hπ.isAdmissible γ c →
      ∀ (v : W) (ℓ : SmoothDual π), ∃ o : G ⧸ Z → ℂ,
        (∀ g : G, o (QuotientGroup.mk g) = ℓ.val (π (g * γ * g⁻¹) v)) ∧
        Integrable o μ ∧
        ∫ q, o q ∂μ = (d : ℂ)⁻¹ * ℓ.val v * c

end Langlands.BaseChange
