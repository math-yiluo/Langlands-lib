import Langlands.BushnellKutzko.ElementFieldInvariants
import Langlands.BushnellKutzko.FundamentalStratum

/-! # Polynomial labels of simple strata at depth `n − 1` -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- The principal-order upper bound in BK94 (1.4) and the formulas (1.5),
printed pp. 112–113. At depth `n − 1`, the monic irreducible factor of the
fundamental polynomial has degree dividing the common layer dimension.
It gives the residue degree, and equality of factors implies conjugacy
up to equivalence. The ramification index is `e(𝔄) / gcd(e(𝔄), n)`. -/
def MinimalSimpleStratumPolynomialStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (L : LatticeChain 𝒪[F] F V) (n : ℤ) (π : RingPrimeElement 𝒪[F]),
    L.IsPrincipal → 1 ≤ n →
    let SimpleStrata := {S : Stratum 𝒪[F] F V //
      S.chain = L ∧ S.n = n ∧ S.r = n - 1 ∧ S.IsSimple}
    let ResiduePolynomial := Polynomial (𝒪[F] ⧸ Ring.jacobson 𝒪[F])
    (∀ S : SimpleStrata, ∃ (f : ResiduePolynomial) (a : ℕ),
      f.Monic ∧ Irreducible f ∧ f ≠ Polynomial.X ∧ 0 < a ∧
      S.1.fundamentalPolynomial π = f ^ a ∧
      f.natDegree ∣ Module.finrank F V / L.period ∧
      elementResidueDegree F S.1.b = f.natDegree ∧
      elementRamificationIndex F S.1.b = L.period / Nat.gcd L.period n.natAbs) ∧
    (∀ (S T : SimpleStrata) (f : ResiduePolynomial) (a b : ℕ),
      f.Monic → Irreducible f → 0 < a → 0 < b →
      S.1.fundamentalPolynomial π = f ^ a → T.1.fundamentalPolynomial π = f ^ b →
      ∃ u ∈ L.unitFiltration 0,
        (↑(u⁻¹) : Module.End F V) * S.1.b * (u : Module.End F V) ∈ T.1.coset)

end Langlands.BushnellKutzko
