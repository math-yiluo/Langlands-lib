# Spectrum criteria for proper ideals and units

Over a complete ultrametric normed field `K`, these propositions concern the
actual quotient algebra of each `PresentedStrictAffinoidAlgebra K` and its
bounded multiplicative seminorm spectrum.

- `SpectrumProperIdealStatement K` says that every proper ideal `I` is
  contained in the kernel of some spectrum point. The ideal is not assumed
  closed, prime, or maximal.
- `SpectrumUnitStatement K` says that an element is a unit if and only if its
  value at every spectrum point is nonzero.
- `SpectrumFiniteUnitIdealStatement K` says that the ideal spanned by the range
  of a tuple `f : Fin m → P` is the unit ideal if and only if every spectrum
  point has nonzero value on at least one member of the tuple.
- `SpectrumIdealCriterionStatement K` is exactly the conjunction of those
  three propositions.

All four declarations are in
`Langlands.Analytic.PresentedStrictAffinoidAlgebra`. They are proposition
definitions, with no proofs asserted in this file. There is no supplied point,
maximal-ideal realization, spectral invertibility hypothesis, or assumed
conclusion. Trivial scalar valuations, zero variables, nonreduced algebras, and
the zero quotient are allowed.

In the zero algebra there are no proper ideals or spectrum points, every
element is a unit, and every tuple spans the unit ideal. Thus all clauses retain
their intended meaning. For `m = 0` the finite-generator criterion says that the
zero ideal is the unit ideal exactly when the spectrum is empty; in a nonzero
strict affinoid, both sides are false.

## Source and derivation

The retained fourteen-page notes of part of Vladimir Berkovich's course,
*Affinoid algebras*, give a canonical injection `Max(A) → M(A)` immediately
before Proposition 2.5.6 on printed/PDF page 9, citing Corollary 2.4.3 on page 7.
The point attached to a maximal ideal has that ideal as its kernel. A proper
ideal is contained in a maximal ideal, giving the first target. The remaining
targets follow from the elementary criteria that an element is a nonunit
exactly when its principal ideal is proper, and that a generated ideal is
contained in a point's kernel exactly when all its generators vanish there.
Conversely a point's kernel is proper since its value at one is one.

These statements are derived consequences of that source passage and
commutative algebra, not verbatim source theorems. They do not state a
Nullstellensatz, finite residue-field degree, maximality of every spectrum
kernel, or a maximum-modulus theorem. The unit and finite-generator interfaces
were proposed by Worker 36 for rational-domain construction; Worker 56 formulated
the proper-ideal target and the Lean and Markdown statements.

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
