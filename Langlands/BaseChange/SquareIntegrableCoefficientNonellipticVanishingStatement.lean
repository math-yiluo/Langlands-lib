import Langlands.BaseChange.CentralQuotientFormalDegree
import Langlands.JacquetLanglands.RegularElliptic
import Mathlib.RepresentationTheory.Irreducible

/-! # The non-elliptic part of a class function times a square-integrable coefficient -/

namespace Langlands.BaseChange

open JacquetLanglands MeasureTheory

/-- Let `π` be an irreducible representation of `GL_n(F)`, square-integrable modulo the center
`Z`, `μ` a Haar measure on `G / Z`, `v` a vector and `ℓ` a smooth functional of `π`, and `Θ` a
function on `GL_n(F)` invariant under conjugation at regular semisimple elements. If
`gZ ↦ Θ(g) conj ℓ(π(g) v)` is a well-defined `μ`-integrable function on `G / Z`, then its
restriction to the complement of the regular elliptic set is integrable with integral `0`.
By the Weyl integration formula this restriction is a sum over the non-elliptic Cartan
subgroups `T` of integrals over `T / Z` of `|D(t)| Θ(t)` times the orbital integrals of the
conjugate coefficient at the regular elements `t` of `T`, and these orbital integrals vanish
(Clozel 1991, §3, Proposition 5 (i), the Selberg principle). -/
def SquareIntegrableCoefficientNonellipticVanishingStatement.{u, uV} : Prop := by
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
      {W : Type uV} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G W),
      IsSquareIntegrable π → π.IsIrreducible →
      ∀ Θ : G → ℂ, (∀ g a : G, IsRegularSemisimple g → Θ (a⁻¹ * g * a) = Θ g) →
        ∀ (v : W) (ℓ : SmoothDual π) (Ψ : G ⧸ Z → ℂ),
          (∀ g : G, Ψ (QuotientGroup.mk g) = Θ g * star (ℓ.val (π g v))) →
          Integrable Ψ μ →
          ∃ Φ : G ⧸ Z → ℂ,
            (∀ g : G, Φ (QuotientGroup.mk g) =
              if IsRegularElliptic g then 0 else Θ g * star (ℓ.val (π g v))) ∧
            Integrable Φ μ ∧ ∫ q, Φ q ∂μ = 0

end Langlands.BaseChange
