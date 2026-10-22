# Power bounds for concrete affinoid quotients

Author: Worker 56.

The first result accepts a bounded map from an actual finite-variable Tate
algebra, together with a concrete monic polynomial annihilating the target
element. If its coefficients have Gauss norm at most one, it lifts the
polynomial to the actual norm unit-ball subring. The entire image of that
subring is bounded by the norm bound of the given map. The algebraic integral
power-bound lemma then applies. The map need not be injective, finite or
contractive. Its target is any ultrametric normed commutative K-algebra,
possibly the zero algebra, and neither it nor K needs to be complete.

The second result handles the trivially valued coefficient field for every
actual closed-ideal quotient. A Tate series has norm at most one because all
of its coefficients do. The quotient map decreases the norm and is surjective,
so every element of the quotient, and hence every power, has norm at most one.
This proof also covers nilpotents and the zero algebra. It uses no completeness.

The imported `SpectralPowerBoundStatement` records the full target, quantifying over
every actual presented quotient and every element with all spectrum values at
most one. It retains completeness and ultrametricity of the normed coefficient
field and does not assume a nontrivial valuation. It is only a proposition
definition. The proved theorem closes it in the trivial-valuation case. No
theorem in this file closes it in general.

For nontrivial valuations, the monic relation required by the first result is
constructed in separate modules leading to `SpectralPowerBoundProof`. The
source route is Noether normalization followed by
the spectral polynomial theorem. Berkovich's course notes, "2. Affinoid
algebras", Proposition 2.4.1, page 6; Propositions 2.6.4–2.6.5, pages 11–12,
give the corresponding original arguments.
These are undated notes of part of Vladimir Berkovich's course; the
note-taker is unidentified.
Registered source:
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`;
content SHA256
`c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
Retained file:
`literature/Retained original of Berkovich's Affinoid algebras course notes (14 pages).pdf`.
The direct dependencies are the actual `Affinoid` quotient construction, the
bounded-image and monic-relation results in `PowerBounds`, and the Tate Gauss
point. The quotient and Gauss-point constructions are due to Worker 36.
