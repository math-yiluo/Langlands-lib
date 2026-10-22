# Nonemptiness of a strict affinoid spectrum

`Langlands.Analytic.PresentedStrictAffinoidAlgebra.SpectrumNonemptyStatement K`
states that every nonzero presented strict affinoid algebra over a complete
ultrametric normed field `K` has a point of its actual bounded multiplicative
seminorm spectrum.

The algebra is the constructed quotient of a finite-variable unit-radius Tate
algebra by its displayed closed ideal. `Nontrivial P` is an explicit premise.
It excludes the zero quotient, whose spectrum is empty because a multiplicative
seminorm must send zero to zero and one to one. No point, norm extension,
maximal-ideal realization, or nontrivial scalar valuation is supplied as input.
Zero presentation variables and nonreduced algebras are allowed. This file
defines a proposition and does not prove it.

## Source and derivation

The retained fourteen-page notes of part of Vladimir Berkovich's course,
*Affinoid algebras*, state on printed/PDF page 9, immediately before
Proposition 2.5.6, that Corollary 2.4.3 gives a canonical injective map from
`Max(A)` to `M(A)` for a strict affinoid algebra. Corollary 2.4.3 is on page 7.
For a nonzero commutative unital ring a maximal ideal exists, so that inclusion
implies the nonemptiness asserted here. This is a derived consequence, not a
verbatim restatement or a claim that the maximal-ideal inclusion is already
formalized. It preserves trivial valuations. Completeness and the ultrametric
field norm are explicit in the Lean target.

The source is registered as
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
with SHA256
`c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
The retained original is
`literature/Retained original of Berkovich's Affinoid algebras course notes (14 pages).pdf`.
The note-taker and publication date are unidentified.

Each proposition retains `[CompleteSpace K]` as an explicit declaration
parameter. Its complete unapplied signature includes `K`, `NormedField K`,
`IsUltrametricDist K`, and `CompleteSpace K`, in that order.
