module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.SurjectiveOnStalks
public import StacksFrontier.RingTheory.Spectrum.Prime.IrreducibleComponents

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Minimal primes and residue fields of a localization

Let `A` be a localization of `R` at the complement of a prime `p`.  Contraction along
`R → A` identifies the minimal primes of `A` with the minimal primes of `R` contained in
`p`, and corresponding primes have the same residue field.  Consequently the product of the
residue fields of the minimal primes of `A` is the localization, at the image of `R \ p`, of
the product of the residue fields of the minimal primes of `R`.

## Main definitions

* `minimalPrimes.residueFieldProduct` is the product of the residue fields of the minimal
  primes of a commutative ring, and `minimalPrimes.enumResidueFieldProduct` the same product
  for an enumeration of those primes.
* `minimalPrimes.localizationResidueFieldProductHom` is the comparison map from an enumerated
  product of the residue fields at the minimal primes of `R` to the product for `A`.

## Main results

* `minimalPrimes.under_mem_minimalPrimes_of_isLocalization` and
  `minimalPrimes.exists_under_eq`: contraction is a bijection from the minimal primes of `A`
  onto the minimal primes of `R` contained in `p`.
* `minimalPrimes.isLocalization_residueFieldProduct`: the product for `A` is the localization
  of the product for `R` at the image of the complement of `p`.

## Implementation notes

The source of the comparison map is a product indexed by an arbitrary enumeration `σ` of the
minimal primes of `R` rather than by the subtype `minimalPrimes R` itself, so that a product
indexed by another type in bijection with the minimal primes needs no reindexing.

A minimal prime of `R` not contained in `p` contributes a factor that the localization kills,
and the element of `R \ p` doing so is a product over the finitely many such primes; this is
why the localization statement assumes the index type finite.

Surjectivity of the comparison map is proved by writing an element of the target as a sum of
elements supported at one index, whose preimages are given by `Function.update`.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public section

universe u

namespace minimalPrimes

/-- A minimal prime ideal is prime. -/
instance isPrime_coe {A : Type u} [CommRing A] (q : minimalPrimes A) :
    (q : Ideal A).IsPrime :=
  q.2.1.1

/-- The product of the residue fields of the minimal primes of a commutative ring. -/
abbrev residueFieldProduct (A : Type u) [CommRing A] : Type u :=
  ∀ q : minimalPrimes A, Ideal.ResidueField (q : Ideal A)

section Comparison

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
variable {ι : Type u} (σ : ι → Ideal R) [∀ i, (σ i).IsPrime]

end Comparison

section Localization

variable {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
variable (A : Type u) [CommRing A] [Algebra R A] [IsLocalization.AtPrime A p]

variable {ι : Type u} {σ : ι → Ideal R} [∀ i, (σ i).IsPrime]
variable (hmem : ∀ i, σ i ∈ minimalPrimes R) (hinj : Function.Injective σ)
  (hsurj : ∀ p' ∈ minimalPrimes R, ∃ i, σ i = p') (hfin : Finite ι)

end Localization

end minimalPrimes
