# Spectrum criteria at arbitrary positive presentation radii

Worker 56 adapts the published strict-affinoid criterion interface developed
by Workers 36 and 56 to the actual positive-polyradius quotient presentations.
This module defines four propositions. It proves none of them.

## Fields, algebras and spectra

The coefficient field `K : Type u` has `NormedField K`,
`IsUltrametricDist K` and `CompleteSpace K`. Its valuation may be trivial.
Every proposition retains all four parameters explicitly, in that order.

The imported `PresentedAffinoidAlgebra K` stores a finite number of variables,
an arbitrary strictly positive real radius for each variable, and a closed
ideal in the corresponding weighted Tate algebra. Its carrier is the actual
ring quotient by that ideal, with the quotient norm. The imported `Banach`
module proves completeness over complete `K`. Presentation radii need not
lie in the scalar value group or its divisible closure. There is no
reducedness, properness or nonzero-quotient hypothesis on the presentation.

`BanachSpectrum P` is the existing spectrum of normalized bounded
multiplicative seminorms on that normed ring. Each point `x` satisfies
`x 0 = 0`, `x 1 = 1`, multiplicativity, the triangle inequality and
`x a ≤ ‖a‖`. Its `kernel` is the actual ring ideal of elements with value
zero. No points, kernel realizations or invertibility certificates are
supplied as input.

## The four propositions

All names below belong to `Langlands.Analytic.PresentedAffinoidAlgebra`.

- `SpectrumProperIdealStatement K` says that for every presentation `P` and
  every ideal `I : Ideal P` with `I ≠ ⊤`, there exists
  `x : BanachSpectrum P` such that `I ≤ x.kernel`. There is no closedness,
  primality or maximality premise on `I`.
- `SpectrumUnitStatement K` says that for every presentation `P` and element
  `a : P`, `IsUnit a` is equivalent to `x a ≠ 0` for every spectrum point
  `x`.
- `SpectrumFiniteUnitIdealStatement K` says that for every `P`, every
  natural number `m` and every tuple `f : Fin m → P`, the ideal
  `Ideal.span (Set.range f)` equals `⊤` if and only if every spectrum point
  has nonzero value on some `f i`. The index `i` is chosen after `x`.
- `SpectrumIdealCriterionStatement K` is exactly the conjunction of the
  preceding three propositions, in that order.

Each declaration is a `def` returning `Prop`, with an explicit
`[CompleteSpace K]` binder. The file does not contain a proof of any criterion
or introduce a criterion as a hypothesis of another construction.

Zero variables, nilpotents, nonreduced algebras and the zero quotient are
included. In the zero quotient there are no proper ideals or spectrum
points, every element is a unit, and every tuple spans the unit ideal.
For `m = 0` the finite criterion specializes to `⊥ = ⊤` if and only if the
spectrum is empty. Both sides are false in a nonzero affinoid; both are true
in the zero quotient.

## Original source and derived formulation

The registered original is V. G. Berkovich, *Non-archimedean analytic spaces*
(Trieste lectures, 2009), literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Printed and PDF page numbers coincide.

Definition 1.2.3 and Exercise 1.2.4, p. 4, give the bounded multiplicative
seminorm spectrum and its normalization. Definition 2.1.2, p. 7, allows
arbitrary positive radii in an admissible finite Tate presentation. The
Library's closed weighted quotient presentations use the actual quotient
norm, realizing that presentation convention.

Exercise 1.2.7(ii), p. 5, is the unit criterion for a commutative Banach ring.
The proper-ideal criterion is a derived consequence of Fact 2.1.3(i),
p. 7, that every ideal of an affinoid algebra is closed, and Fact 1.2.6,
p. 4, that a nonzero commutative Banach ring has nonempty spectrum. For a
proper ideal `I`, its closed quotient is a nonzero Banach ring; pulling a
spectrum point back along the quotient map gives a point annihilating `I`.
The finite-generator criterion is then an elementary consequence: a proper
generated ideal has such a point, whereas a point's kernel is proper and
cannot contain a tuple generating the unit ideal. The closedness theorem,
quotient argument and these implications explain the provenance; this file
does not implement them or assume them.

The proposition shapes retain the published strict-affinoid interface from
`Langlands.Geometry.Analytic.SpectrumIdealCriterionStatement`, replacing its
unit-radius presentation structure by `PresentedAffinoidAlgebra K`. The
strict statements concern a different carrier family and are not applied as
proofs of the present propositions. The proper-ideal and finite-generator
formulations are derived consequences, rather than verbatim source
statements. They assert neither maximality of spectrum kernels nor finite
residue degree.

The later proof may instead transfer the published strict criterion through
actual radius-realizing scalar extension and bounded quotient descent. No
scalar extension, retraction, faithful-flatness hypothesis or assumed
spectral conclusion appears in these propositions. General domain
representability, atlases, structure sheaves, etale sites, equivariant sites
and the Harris tower remain separate obligations.
