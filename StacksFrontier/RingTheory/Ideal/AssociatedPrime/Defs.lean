module

public import Mathlib.Tactic.CrossRefAttribute
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
public import Mathlib.RingTheory.Support
public import Mathlib.Algebra.Lie.OfAssociative

set_option autoImplicit false
set_option maxSynthPendingDepth 3

@[expose] public section

-- Stacks tag 00LA: https://stacks.math.columbia.edu/tag/00LA

variable (R : Type*) [CommRing R]
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- **Stacks 00LA**.
A prime ideal `p` of `R` is associated to the `R`-module `M` when it is the
annihilator of a single element of `M`. -/
@[stacks 00LA]
def IsAssociatedPrimeStacks (p : Ideal R) : Prop :=
  p.IsPrime ∧ ∃ m : M, (⊥ : Submodule R M).colon (Submodule.span R {m}) = p

/-- The set of prime ideals of `R` associated to the `R`-module `M`. -/
def assStacks : Set (Ideal R) :=
  {p : Ideal R | IsAssociatedPrimeStacks R M p}

/-- An ideal lies in `assStacks R M` iff it is prime and is the annihilator of
some element of `M`. -/
@[simp]
theorem mem_assStacks_iff {p : Ideal R} :
    p ∈ assStacks R M ↔
      p.IsPrime ∧ ∃ m : M, (⊥ : Submodule R M).colon (Submodule.span R {m}) = p :=
  Iff.rfl

-- ===== merged from StacksDraft.Ch10.Sec63.Tag0586 =====

/-!
# Associated primes lie in the support

Let `R` be a commutative ring and `M` an `R`-module. A prime ideal `p ⊆ R` is an
*associated prime* of `M` if some element `x ∈ M` has annihilator exactly `p`, that is
`p = Ann_R(x) = {a ∈ R | a • x = 0}`; the set of these is
`Ass(M) = {p ∈ Spec(R) | ∃ x ∈ M, p = Ann_R(x)}`. The *support* of `M` is the set of
primes at which `M` localizes to something nonzero,
`Supp(M) = {p ∈ Spec(R) | M_p ≠ 0}`, where `M_p` is the localization of `M` at the
multiplicative set `R \ p`.

## Main definitions

* `assAssociatedPrimes R M`: the set `Ass(M)`, as a subset of `PrimeSpectrum R`.

## Main results

* `assPrimes_subset_support` (Stacks tag 0586): `Ass(M) ⊆ Supp(M)`.

If `p = Ann_R(x)`, then `r ↦ r • x` has kernel `Ann_R(x) = p`, so `x` generates a
submodule isomorphic to `R ⧸ p` and hence `R ⧸ p ↪ M`. Localization is exact, so
`(R ⧸ p)_p = κ(p) ≠ 0` injects into `M_p`, giving `M_p ≠ 0`.

## Implementation notes

The support is Mathlib's `Module.support R M : Set (PrimeSpectrum R)`, characterized by
`p ∈ Module.support R M ↔ Nontrivial (LocalizedModule p.asIdeal.primeCompl M)`.

Associated primes are indexed by `PrimeSpectrum R`, so primality is built into the
type, and the annihilator is `Module.annihilator R (Submodule.span R {x})`. Following
the Stacks project and Bourbaki, this annihilator is required to equal `p` *exactly*,
not merely to have radical `p`.
-/

@[expose] public section

-- ===== merged from StacksDraft.Ch10.Sec63.Tag05BY =====

/-!
# Associated primes of a module over a quotient ring

Let `R` be a commutative ring, `I ⊆ R` an ideal and `M` a module over `R ⧸ I`, hence
also an `R`-module through `π : R → R ⧸ I`. Contraction along `π` identifies the
associated primes of `M` over `R ⧸ I` with those over `R`. This is Stacks tag 05BY.

A prime `p ⊆ R` is *associated* to `M` when `p = Ann_R(m) = {r | r • m = 0}` for some
`m ∈ M`; this is the classical (non-radical) definition.

## Main definitions

* `Stacks.AssociatedPrimes.assPrimes R M`: the set of primes associated to `M`.

The annihilator `Ann_R(m)` is Mathlib's `Ideal.torsionOf R M m`.

## Main results

* `Stacks.AssociatedPrimes.torsionOf_eq_comap`: `Ann_R(m) = π⁻¹(Ann_{R ⧸ I}(m))`, because the
  `R`-action on `M` factors through `π`.
* `Stacks.AssociatedPrimes.ideal_le_of_mem_assPrimes`: every associated prime of `M` over `R`
  contains `I`, since `I` acts as zero on `M`.
* `Stacks.AssociatedPrimes.mem_assPrimes_quotient_iff_comap_mem_assPrimes`: a prime `p̄` of
  `R ⧸ I` is associated to `M` iff `π⁻¹(p̄)` is associated to `M` over `R`.
* `Stacks.AssociatedPrimes.main_theorem_05by`: contraction along `π` carries `Ass_{R ⧸ I}(M)`
  onto `Ass_R(M)`, that is `π⁻¹(Ass_{R ⧸ I}(M)) = Ass_R(M)` as sets of ideals
  of `R`.
-/

@[expose] public section

open Submodule

namespace Stacks.AssociatedPrimes

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module (R ⧸ I) M] [Module R M]
  [IsScalarTower R (R ⧸ I) M]

end Stacks.AssociatedPrimes

-- ===== merged from StacksDraft.Ch10.Sec66.Tag0589 =====

/-!
# Associated primes, weakly associated primes and the support

Let `R` be a commutative ring (with unit) and let `M` be an `R`-module. For `m ∈ M`,
the annihilator of `m` is the ideal `Ann(m) = { f ∈ R | f • m = 0 }`, and for a prime ideal
`p` of `R` we write `M_p` for the localization of `M` at `p`. We consider three sets of
prime ideals:

1. Associated primes `Ass(M)`: primes `p` such that there exists `m ∈ M` with
   `Ann(m) = p`. (Stacks tag 00LA.)
2. Weakly associated primes `WeakAss(M)`: primes `p` such that there exists `m ∈ M`
   with `p` minimal among the prime ideals containing `Ann(m)`. (Stacks tag 0547.)
3. Support `Supp(M)`: primes `p` such that `M_p ≠ 0`. (Stacks tag 00L1.)

Stacks tag 0589 (Lemma 10.66.6): `Ass(M) ⊆ WeakAss(M) ⊆ Supp(M)`. No hypotheses such as
Noetherianity of `R` or finiteness of `M` are required.

All three sets are indexed by `PrimeSpectrum R`, matching Mathlib's `Module.support`, so
that the inclusions are genuine subset relations in `Set (PrimeSpectrum R)`. The
annihilator `Ann(m)` is `(R ∙ m).annihilator`, the annihilator of the cyclic submodule
generated by `m`, which satisfies `f ∈ (R ∙ m).annihilator ↔ f • m = 0`. Minimality of `p`
among the primes containing `Ann(m)` is encoded as `p.asIdeal ∈ (Ann m).minimalPrimes`, and
the support is Mathlib's `Module.support R M`, i.e.
`{ p | Nontrivial (LocalizedModule p.asIdeal.primeCompl M) }`.

Mathlib's `IsAssociatedPrime`/`associatedPrimes` use the *radical* of the annihilator, a
deliberately non-standard convention; `Ass` below uses the strict condition `Ann(m) = p`
instead.
-/

@[expose] public section

namespace StacksProblem

end StacksProblem
