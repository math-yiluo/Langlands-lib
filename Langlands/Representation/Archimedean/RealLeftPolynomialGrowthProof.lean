import Langlands.Representation.Archimedean.RealLeftPolynomialGrowth
import Langlands.Representation.Archimedean.RealRootPolynomialGrowth

/-!
# Proof of `RealLeftPolynomialGrowthStatement`

The statement is the case `c₀ = (p + 1, p)` of
`RootPolynomial.finrank_map_le_of_isRootPoly` (module `RealRootPolynomialGrowth`): the element
`lowerRootElement n p hp t` is `RootPolynomial.rootUnit _ t`, and a function that is a polynomial
of degree `< k` along every `t ↦ e(t) g` satisfies `RootPolynomial.IsRootPoly`
(`RootPolynomial.isRootPoly_of_polynomial`).
-/

set_option autoImplicit false

namespace Langlands.Archimedean

open RootPolynomial in
/-- Proof of `RealLeftPolynomialGrowthStatement`. -/
theorem realLeftPolynomialGrowth : RealLeftPolynomialGrowthStatement := by
  intro n ds p k hp Y hY
  have hc₀ : ((⟨p + 1, hp⟩, ⟨p, Nat.lt_of_succ_lt hp⟩) : Fin n × Fin n).2 <
      ((⟨p + 1, hp⟩, ⟨p, Nat.lt_of_succ_lt hp⟩) : Fin n × Fin n).1 :=
    Fin.mk_lt_mk.2 (Nat.lt_succ_self p)
  have he : ∀ t : ℝ, lowerRootElement n p hp t = rootUnit hc₀ t := fun _ => Units.ext rfl
  exact finrank_map_le_of_isRootPoly ds hc₀ k Y fun h hh =>
    isRootPoly_of_polynomial hc₀ fun g => by
      obtain ⟨q, hq, hqt⟩ := hY h hh g
      exact ⟨q, hq, fun t => by rw [← he]; exact hqt t⟩

end Langlands.Archimedean
