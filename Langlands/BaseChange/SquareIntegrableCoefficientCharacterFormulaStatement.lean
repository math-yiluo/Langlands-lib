import Langlands.BaseChange.CentralQuotientFormalDegree
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TraceCoefficientFamily
import Langlands.JacquetLanglands.LocalCharacter
import Langlands.JacquetLanglands.RegularElliptic
import Mathlib.RepresentationTheory.Irreducible

/-! # The character formula for a conjugate square-integrable coefficient of `GL_n` -/

namespace Langlands.BaseChange

open JacquetLanglands MeasureTheory HarishChandraSchwartz

/-- Let `ρ` be an irreducible representation of `GL_n(F)`, square-integrable modulo the center
`Z`. There is a function `Θ` on `GL_n(F)` whose value at every regular semisimple element is the
character value of `ρ` there, with the following property. For every irreducible `π`,
square-integrable modulo `Z` with the same unitary central character, every Haar measure `μ` on
`G / Z`, vector `v` and smooth functional `ℓ` of `π`, the function
`gZ ↦ Θ(g) conj ℓ(π(g) v)` is well defined and `μ`-integrable on `G / Z`, and its integral is
the trace of `ρ` on the conjugate coefficient `f(g) = conj ℓ(π(g) v)`: for every compact open
subgroup `H` fixing `v` it equals `∫_{G/Z} ψ^ρ_H(g) f(g) dμ`, where
`ψ^ρ_H(g) = trace(e_H ρ(g) e_H)` is the trace coefficient of `ρ`. This is Clozel's formula
(3.1) for `f` in the Schwartz space `C(G, ξ⁻¹)` (Clozel 1991, §3, Corollary 4 and the proof of
Theorem 3). -/
def SquareIntegrableCoefficientCharacterFormulaStatement.{u, uV} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] (n : ℕ), 0 < n →
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    let G := GeneralLinear n F
    let Z := Subgroup.center G
    letI := centralQuotientMeasurableSpace F n
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (hρ : IsSquareIntegrable ρ), ρ.IsIrreducible →
      ∃ Θ : G → ℂ,
        (∀ g : G, IsRegularSemisimple g → HasCharacterValue ρ hρ.isAdmissible g (Θ g)) ∧
        ∀ (μ : Measure (G ⧸ Z)) [μ.IsHaarMeasure]
          {W : Type uV} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G W),
          IsSquareIntegrable π → π.IsIrreducible →
          ∀ (cρ : UnitaryCentralCharacter ρ) (cπ : UnitaryCentralCharacter π),
            cρ.character = cπ.character →
            ∀ (v : W) (ℓ : SmoothDual π), ∃ Ψ : G ⧸ Z → ℂ,
              (∀ g : G, Ψ (QuotientGroup.mk g) = Θ g * star (ℓ.val (π g v))) ∧
              Integrable Ψ μ ∧
              ∀ (H : CompactOpenSubgroup G), v ∈ fixedVectors π H.toSubgroup →
                ∀ T : G ⧸ Z → ℂ,
                  (∀ g : G, T (QuotientGroup.mk g) =
                    traceCoefficient ρ hρ.isAdmissible.1 H g * star (ℓ.val (π g v))) →
                  ∫ q, Ψ q ∂μ = ∫ q, T q ∂μ

end Langlands.BaseChange
