module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Killing an ideal of nilpotents changes neither the spectrum nor heights

Let `I` be an ideal of a commutative ring `R` consisting of nilpotent elements, that is
`I ≤ nilradical R`. Every prime of `R` contains `I`, so contraction along `R → R ⧸ I` is an
order isomorphism `Spec (R ⧸ I) ≃ Spec R`; consequently the height of a prime is unchanged by
the quotient, and adding `I` to an ideal does not change its minimal primes.

## Main definitions

* `PrimeSpectrum.comapQuotientMkOrderIso`: the order isomorphism
  `Spec (R ⧸ I) ≃o Spec R` for `I ≤ nilradical R`.

## Main results

* `Ideal.height_comap_quotientMk_of_le_nilradical`: the height of a prime of `R ⧸ I` equals the
  height of its contraction to `R`.
* `Ideal.minimalPrimes_sup_of_le_nilradical`: `(J ⊔ I).minimalPrimes = J.minimalPrimes`.
* `Ideal.mem_minimalPrimes_comap_quotientMk_of_le_nilradical`: a minimal prime over the image of
  `J` in `R ⧸ I` contracts to a minimal prime over `J`.
* `Ideal.le_height_of_mem_minimalPrimes_map_quotientMk`: a height bound on the minimal primes of
  `J` in `R` is inherited by the minimal primes of its image in `R ⧸ I`.
* `Ideal.minimalPrimes_map_quotientMk_of_le_nilradical`: extension along `R → R ⧸ I` is a
  bijection from the minimal primes over `J` onto those over the image of `J`.
* `Ideal.exists_mem_minimalPrimes_map_quotientMk_height_eq`: if some minimal prime over `J` has
  height `e`, then so does some minimal prime over the image of `J` in `R ⧸ I`.

## Implementation notes

Bijectivity of the contraction is Mathlib's
`PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical`; what is added here is that it
reflects the order, which follows from `Ideal.map_comap_of_surjective` because the quotient map
is surjective. The height statement is then
`Order.height_orderIso` read through `PrimeSpectrum.height_eq_orderHeight`.

The statement about minimal primes is obtained from `Ideal.radical_minimalPrimes`: adding an
ideal of nilpotents does not change the radical, because `I ≤ nilradical R ≤ J.radical`.
-/

@[expose] public noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- **A ring isomorphism carries the nilradical to the nilradical.** This is
`Ideal.map_radical_of_surjective` at the zero ideal. -/
theorem Ideal.map_nilradical {S : Type*} [CommRing S] (e : R ≃+* S) :
    (nilradical R).map (e : R →+* S) = nilradical S := by
  rw [nilradical, nilradical, Ideal.zero_eq_bot, Ideal.zero_eq_bot,
    Ideal.map_radical_of_surjective e.surjective (by rw [RingHom.ker_coe_equiv]),
    Ideal.map_bot]

/-- **A ring isomorphism induces one of the reductions.** -/
def RingEquiv.quotientNilradical {S : Type*} [CommRing S] (e : R ≃+* S) :
    (R ⧸ nilradical R) ≃+* (S ⧸ nilradical S) :=
  Ideal.quotientEquiv _ _ e (Ideal.map_nilradical e).symm

/-- The isomorphism `RingEquiv.quotientNilradical e` sends the class of `x` to the class of
`e x`. -/
@[simp]
theorem RingEquiv.quotientNilradical_mk {S : Type*} [CommRing S] (e : R ≃+* S) (x : R) :
    e.quotientNilradical (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (e x) :=
  rfl

end
