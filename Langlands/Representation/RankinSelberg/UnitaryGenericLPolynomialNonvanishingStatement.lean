import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Representation.Unitary.Basic

/-!
# Nonvanishing of the L-polynomial of a unitary generic pair on `Re(s) ≥ 1`

The non-Archimedean half of Getz–Hahn, Theorem 11.5.2: for irreducible
admissible generic unitary representations `π` and `σ` of general linear groups
over a p-adic field, `L(s, π × σ)` is holomorphic and nonzero for `Re(s) ≥ 1`.
With `L(s, π × σ) = P(q^(-s))⁻¹`, this says that every polynomial `P` satisfying
the symmetric pair L-polynomial relation has no zero at `q^(-s)` when
`Re(s) ≥ 1`. It is a statement, not a proof, and it does not assert that the
L-polynomial exists.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Polynomial

universe uF uV uW

/-- Getz–Hahn, Theorem 11.5.2, non-Archimedean case (printed page 305): for
irreducible admissible generic unitarizable `π` of `GL_(r+1)(F)` and `σ` of
`GL_(t+1)(F)`, of any ranks, every polynomial `P` satisfying the symmetric pair
L-polynomial relation satisfies `P(q^(-s)) ≠ 0` whenever `1 ≤ Re(s)`, where `q`
is the residue cardinality of `F`. Existence of `P` is not asserted. -/
def UnitaryGenericLPolynomialNonvanishingStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W),
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ r π) →
    IsUnitarizable π →
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ t σ) →
    IsUnitarizable σ →
    ∀ P : ℂ[X], IsPadicSymmetricLPolynomial F ψ ν.val π σ P →
      ∀ s : ℂ, 1 ≤ s.re →
        P.eval ((F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-s)) ≠ 0

end Langlands.RankinSelberg
