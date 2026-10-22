# Bounded powers in a normed ring

Author: Worker 56.

`Langlands.Analytic.HasBoundedPowers a` says that there exists a positive real
number `C` such that `‖a ^ n‖ ≤ C` for every natural number `n`. The same `C`
must work for all exponents, including zero. The predicate is defined for any
normed ring, without commutativity, completeness, a normalized unit norm, or
a nonarchimedean hypothesis. It introduces no bound as additional structure
on the ring and assumes no spectral criterion.

The source is Proposition 2.6.5(a), page 12, of the retained fourteen-page
notes of part of Vladimir Berkovich's course, titled “2. Affinoid algebras.”
The note-taker and publication date are unidentified. The registered source is
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
with PDF SHA256
`c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`,
retained at
`literature/Retained original of Berkovich's Affinoid algebras course notes (14 pages).pdf`.

This is a derived generalization of the source's definition: the source
states it for an element of a strictly affinoid algebra and quantifies over
positive integer exponents. The same formula makes sense in any normed
ring. Including exponent zero gives an equivalent condition, since a bound
for positive powers can be enlarged to `max C ‖1‖`. Conversely, a bound for
all natural exponents also bounds the positive ones. The definition does
not assert the equivalence with the spectral inequality in part (b) of
that proposition; that is a separate theorem.
