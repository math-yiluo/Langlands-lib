import Langlands.BushnellKutzko.Stratum

/-! # Fundamental strata and their polynomials

BK93 §2.3, printed pp. 57–58, including Definition (2.3.3).
-/

noncomputable section

namespace Langlands.BushnellKutzko

universe uO uK uV

variable (O : Type uO) [CommRing O]

/-- A nonzero generator of the maximal ideal, written as the Jacobson radical
to use the same integer-ring mechanism over extension fields. -/
abbrev RingPrimeElement :=
  {π : O // π ≠ 0 ∧ Ideal.span ({π} : Set O) = Ring.jacobson O}

variable (K : Type uK) [Field K] [Algebra O K]

open scoped Classical in
/-- Coefficientwise reduction of an integral polynomial from `K` to the residue ring of `O`.
The value of a coefficient with no lift to `O` is set to zero, making this construction total.
In the intended injective integer-ring inclusions, every lift is unique. -/
def reduceIntegralPolynomial (p : Polynomial K) : Polynomial (O ⧸ Ring.jacobson O) :=
  ∑ i ∈ p.support, Polynomial.monomial i
    (if h : ∃ a : O, algebraMap O K a = p.coeff i then
      Ideal.Quotient.mk (Ring.jacobson O) (Classical.choose h)
    else 0)

variable {O K} {V : Type uV} [AddCommGroup V] [Module K V]
  [Module O V] [IsScalarTower O K V]

namespace Stratum

/-- A fundamental stratum has `r = n−1` and its coset contains no nilpotent
endomorphism (BK93 p. 57). -/
def IsFundamental (S : Stratum O K V) : Prop :=
  S.r = S.n - 1 ∧ ∀ x ∈ S.coset, ¬ IsNilpotent x

/-- The element `y_b = b^{e/g} π^{n/g}`, where `e = e(𝔄)` and
`g = gcd(e,n)` (BK93 pp. 57–58). -/
def fundamentalElement (S : Stratum O K V) (π : RingPrimeElement O) : Module.End K V :=
  let e := S.chain.period
  let g := Nat.gcd e S.n.natAbs
  (algebraMap O K π.1 ^ (S.n / (g : ℤ))) • S.b ^ (e / g)

/-- The polynomial `φ_b` of BK93 p. 58, using its equivalent construction
as the reduction of the `K`-characteristic polynomial of `y_b`. -/
def fundamentalPolynomial (S : Stratum O K V) (π : RingPrimeElement O) :
    Polynomial (O ⧸ Ring.jacobson O) :=
  letI := S.chain.finiteDimensional
  reduceIntegralPolynomial O K (S.fundamentalElement π).charpoly

/-- A split fundamental stratum: `φ_b` has two distinct monic irreducible
factors (BK93 (2.3.3), p. 58). -/
def IsSplit (S : Stratum O K V) : Prop :=
  S.IsFundamental ∧ ∃ π : RingPrimeElement O,
    ∃ p q : Polynomial (O ⧸ Ring.jacobson O),
      p.Monic ∧ q.Monic ∧ Irreducible p ∧ Irreducible q ∧ p ≠ q ∧
      p ∣ S.fundamentalPolynomial π ∧ q ∣ S.fundamentalPolynomial π

/-- A nonsplit fundamental stratum: `φ_b` is a positive power of one monic
irreducible polynomial (BK93 (2.3.3), p. 58). -/
def IsNonsplit (S : Stratum O K V) : Prop :=
  S.IsFundamental ∧ ∃ π : RingPrimeElement O,
    ∃ (p : Polynomial (O ⧸ Ring.jacobson O)) (m : ℕ),
      p.Monic ∧ Irreducible p ∧ 0 < m ∧ S.fundamentalPolynomial π = p ^ m

end Stratum

end Langlands.BushnellKutzko
