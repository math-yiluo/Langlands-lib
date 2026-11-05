# The nilradical and generic prime of an actual lifted finite free model

This derived construction implements the prime-nilradical and unique-generic-prime
part of the monic-model step in Stacks Lemma 37.24.8 (tag 0551), registered source
`stacks-generic-geometric-irreducibility-2026-11-04`, `0551.html`, proof.
It extends the actual `FiniteSeparableLiftedPolynomialModel`; no new existence
hypothesis or abstract scheme model is introduced.

Let `R` be any commutative ring for which `PrimeSpectrum R` is irreducible.
The equivalence `PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical` makes
`nilradical R` a prime ideal, so the actual quotient `D = R / nilradical R` is a
domain. Let `K` be a specified fraction field of `D` and let `L/K` be a finite
separable extension. The original `D`- and `K`-algebra structures on `L` are
compatible. The rings `R`, `K`, and `L` may occupy three independent universes.
There is no reducedness, domain, Noetherianity, characteristic, or normality
assumption on `R`.

`FiniteSeparableNilradicalModel` is an abbreviation for the actual lifted monic
model with coefficient quotient literally `R / nilradical R`.
`finiteSeparableNilradicalModel` constructs it by applying the proved lifted-model
constructor to the surjective quotient map. Its carrier is literally the quotient
`R[X] / (polynomial)` and inherits the finite, free, and finite-presentation
instances from that construction. Its reduction comparison is the same actual
domain subalgebra inside the original `L`.

The general helper `ker_includeRight_quotient` proves that tensoring an
`R`-algebra `A` with `R/I` kills exactly the ideal `I A`. The proof identifies
this tensor inclusion with quotient projection followed by Mathlib's explicit
quotient/tensor algebra equivalence and computes the kernel. No flatness or
finiteness assumption is needed for this helper.

`ker_reductionMap` specializes this computation and cancels the proved reduction
equivalence. It identifies the reduction kernel with the extended ideal
`(nilradical R).map (algebraMap R Carrier)`. Mapping radicals shows this ideal is
contained in the carrier's nilradical. The reduction target is an actual
subalgebra of the field `L`, hence a domain, so the kernel is prime and contains
the carrier's nilradical. Thus `ker_reductionMap_eq_nilradical` proves equality.
The ideal is nil; no uniform nilpotence exponent is asserted.

`reducedEquiv` constructs an actual ring equivalence from
`Carrier / nilradical Carrier` to the original domain subalgebra. The theorem
`reducedEquiv_mk` identifies its composite with quotient projection as the
original reduction map. `isHomeomorph_reduction` proves that the actual map on
prime spectra induced by coefficient reduction is a homeomorphism, using its
proved surjectivity and nil kernel. This is a comparison of the spectra's
topological spaces, not an isomorphism from the potentially nonreduced model
scheme to its reduction.

`irreducibleSpectrum` proves irreducibility because the carrier nilradical is
prime. `genericPrime` is explicitly the prime ideal given by the reduction
kernel; `genericPrime_asIdeal` identifies it with the nilradical. The theorem
`isGenericPoint_genericPrime` computes the closure of its singleton as the whole
spectrum. `genericPrime_under` computes its contraction to `R` as exactly
`nilradical R`: the coefficient formula for the reduction map and injectivity of
the original domain map into the domain model reduce this to the quotient-map
kernel calculation.

Finally, `prime_eq_genericPrime` proves uniqueness among all prime ideals over
the base nilradical. Every prime contains the carrier nilradical. The carrier is
module finite over `R`, so it is quasi-finite; Mathlib's incomparability theorem
for quasi-finite algebras identifies two comparable primes with the same
contraction. This proves the source's unique-prime assertion without an added
reducedness hypothesis. The comparison lemmas apply whenever the specified model
is supplied; the irreducible-base assumption is used by its constructor.

Identifying the actual generic residue-field extension, proving etaleness at
this prime, finite closed-image shrinking, the scheme cover, and splitting the
geometric irreducible components remain further obligations. This unit does not
claim full Stacks 0551 or completion of Conrad's geometric-fibre results.
