import Langlands.BaseChange.CentralQuotientFormalDegree
import Langlands.JacquetLanglands.LocalCharacter
import Langlands.JacquetLanglands.RegularElliptic
import Mathlib.RepresentationTheory.Irreducible

/-! # The elliptic part of the trace of a square-integrable coefficient of `GL_n` -/

namespace Langlands.BaseChange

open JacquetLanglands MeasureTheory

/-- Let `ρ` and `π` be irreducible representations of `GL_n(F)`, square-integrable modulo the
center `Z`, with the same unitary central character, `d` the formal degree of `π` for a Haar
measure `μ` on `G / Z`, and `Θρ` the character values of `ρ` on the regular elliptic set. For
every vector `v` and smooth functional `ℓ` of `π`, the product of `Θρ` with the conjugate
coefficient `g ↦ conj ℓ(π(g) v)`, extended by zero off the regular elliptic set, descends to
`G / Z`, is integrable, and its integral is `d⁻¹ conj ℓ(v)` if `ρ ≅ π` and `0` otherwise.
This is the trace of `ρ` on the conjugate coefficient (Schur orthogonality) computed by the
character formula on the Schwartz space, of which only the regular elliptic part survives
(Clozel 1991, §3: Corollary 4, Proposition 5 (i) and the proof of Theorem 3). -/
def EllipticCoefficientTraceStatement.{u, uV} : Prop := by
  classical
  exact ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] (n : ℕ), 0 < n →
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    let G := GeneralLinear n F
    let Z := Subgroup.center G
    letI := centralQuotientMeasurableSpace F n
    ∀ (μ : Measure (G ⧸ Z)) [μ.IsHaarMeasure]
      {V W : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ G V) (π : Representation ℂ G W)
      (hρ : IsSquareIntegrable ρ) (_hπ : IsSquareIntegrable π),
      ρ.IsIrreducible → π.IsIrreducible →
      ∀ (cρ : UnitaryCentralCharacter ρ) (cπ : UnitaryCentralCharacter π),
        cρ.character = cπ.character →
        ∀ d : ℝ, IsCentralFormalDegree μ π d →
        ∀ Θρ : {g : G // IsRegularElliptic g} → ℂ,
          (∀ g, HasCharacterValue ρ hρ.isAdmissible g.val (Θρ g)) →
          ∀ (v : W) (ℓ : SmoothDual π), ∃ Φ : G ⧸ Z → ℂ,
            (∀ g : G, Φ (QuotientGroup.mk g) =
              if h : IsRegularElliptic g then Θρ ⟨g, h⟩ * star (ℓ.val (π g v)) else 0) ∧
            Integrable Φ μ ∧
            (∫ q, Φ q ∂μ) = if Nonempty (ρ.Equiv π) then (d : ℂ)⁻¹ * star (ℓ.val v) else 0

end Langlands.BaseChange
