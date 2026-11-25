module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Going up or going down plus surjectivity forces a dimension inequality

Let `φ : R → S` be a map of commutative rings with unit. A prime `q` of `S` *lies over* a
prime `p` of `R` when `φ⁻¹(q) = p`, i.e. `p` is the contraction of `q` along `φ`, and the
induced map `Spec(S) → Spec(R)` sends `q ↦ φ⁻¹(q)`.

## Main results

If `φ` satisfies either going up or going down, and the induced map `Spec(S) → Spec(R)`
is surjective, then `dim(R) ≤ dim(S)`.

The disjunction is inclusive — one of the two hypotheses suffices — so it is recorded as
two statements, `ringKrullDim_le_of_goingUp` and `ringKrullDim_le_of_goingDown`. Krull
dimension is `ringKrullDim`, valued in the extended natural numbers `WithBot ℕ∞`, whose
ordering handles the degenerate zero-ring case `⊥` uniformly.

Surjectivity of `Spec(S) → Spec(R)` is expressed through
`PrimeSpectrum.comap φ : PrimeSpectrum S → PrimeSpectrum R`: it says precisely that every
prime `p` of `R` has a prime `q` of `S` with `φ⁻¹(q) = p`, that is, lying over `p`.

## Proof outline

Assume going up and take a chain of primes `p₀ ⊊ p₁ ⊊ ⋯ ⊊ p_e` in `R`. Surjectivity
gives a prime `q₀` of `S` lying over `p₀`, and going up extends this inductively to
`q₀ ⊆ q₁ ⊆ ⋯ ⊆ q_e` with `q_i` lying over `p_i`. Since the `p_i` increase strictly and
`q_i` contracts to `p_i`, the `q_i` increase strictly too, so `q₀ ⊊ ⋯ ⊊ q_e` is a chain
of length `e` in `S`. Hence `dim(S) ≥ e` for every chain length `e` realized in `R`,
giving `dim(S) ≥ dim(R)`. Going down is analogous, building the chain downward from a
prime lying over `p_e`.
-/

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S]

open Order

-- ===== merged from Sec112/Tag00OI =====

/-!
# Homomorphisms and dimension: going up and maximal ideals

Let `φ : R → S` be a ring homomorphism of commutative rings.

A prime ideal `q ⊆ S` *lies over* a prime ideal `p ⊆ R` if the inverse image
(contraction) of `q` under `φ` equals `p`, i.e. `φ⁻¹(q) = p`. For any prime ideal
`q ⊆ S` its contraction `φ⁻¹(q)` is automatically a prime ideal of `R`; see
`Ideal.comap_isPrime`.

The ring map `φ` satisfies *going up* if, given prime ideals `p ⊆ p'` in `R` and a
prime ideal `q` in `S` lying over `p`, there exists a prime ideal `q'` of `S` with
`q ⊆ q'` which lies over `p'`.

## Main definitions

* `LiesOver`: a prime ideal of `S` lies over a prime ideal of `R` under `φ`.
* `GoingUp`: the going up property of a ring map.

## Main results

* `comap_isMaximal_of_goingUp`: if `φ` satisfies going up and `q ⊆ S` is a maximal
  ideal, then its inverse image `φ⁻¹(q) ⊆ R` is a maximal ideal of `R`.
-/

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S]

-- ===== merged from Sec112/Tag00OJ =====

/-!
# Homomorphisms and dimension: integral ring maps

Let `R` and `S` be commutative rings and let `f : R → S` be a ring homomorphism such
that `S` is integral over `R`, that is, every `s ∈ S` is a root of a monic polynomial
with coefficients in `f(R)` (in Mathlib, `RingHom.IsIntegral f`). Then

1. `dim(R) ≥ dim(S)`, equivalently `ringKrullDim S ≤ ringKrullDim R`;
2. every closed point of `Spec(S)` maps to a closed point of `Spec(R)` under the
   induced map `Spec(f) = PrimeSpectrum.comap f`.

Here `dim(A)` is the Krull dimension `ringKrullDim A`, the supremum over chains of
prime ideals `𝔭₀ ⊊ ⋯ ⊊ 𝔭ₙ` of their length `n`, valued in `WithBot ℕ∞` and equal to
`-∞` only for the zero ring. The spectrum `Spec(A) = PrimeSpectrum A` is the set of
prime ideals of `A` with the Zariski topology, and a ring map `f : R → S` induces the
continuous map `PrimeSpectrum.comap f : Spec(S) → Spec(R)` sending `𝔮` to `f⁻¹(𝔮)`. A
point `x ∈ Spec(A)` is closed when `{x}` is closed, equivalently when `x.asIdeal` is a
maximal ideal of `A`.

The inequality is oriented so that `dim(R) ≥ dim(S)` reads as
`ringKrullDim S ≤ ringKrullDim R` for Mathlib's `≤` on `WithBot ℕ∞`; it holds because
contraction along `f` sends strict chains of primes in `S` to strict chains in `R`. No
injectivity, surjectivity or finiteness hypothesis on `f` is needed beyond
integrality.
-/

@[expose] public section

/-- **Stacks Tag 00OJ.** If `f : R → S` is a ring map making `S` integral over `R`,
then `ringKrullDim S ≤ ringKrullDim R` and every closed point of `Spec(S)` contracts
to a closed point of `Spec(R)`. -/
@[stacks 00OJ]
theorem integral_dim_up
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R ∧
    ∀ q : PrimeSpectrum S, IsClosed ({q} : Set (PrimeSpectrum S)) →
      IsClosed ({PrimeSpectrum.comap f q} : Set (PrimeSpectrum R)) := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  have halg : algebraMap R S = f := rfl
  constructor
  · -- (a) dimension inequality via strict monotonicity of the contraction map
    refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f) ?_
    intro p q hpq
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hpq ⊢
    rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal, ← halg]
    have := p.isPrime
    exact Ideal.IsIntegral.under_lt_under hpq
  · -- (b) closed points map to closed points (maximal contracts to maximal)
    intro q hq
    rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal] at hq ⊢
    rw [PrimeSpectrum.comap_asIdeal, ← halg]
    have := hq
    exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal q.asIdeal
