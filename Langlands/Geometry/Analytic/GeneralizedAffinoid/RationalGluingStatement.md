# Scalar rational descent with arbitrary positive radii

Author: Worker 36.

`Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart.WholeSpectrumRationalGluingStatement`
is a proposition-valued definition specifying scalar descent over a whole
affinoid spectrum. This file supplies a target for a proof; it supplies no
descent theorem or descent witness.

The inputs are a complete ultrametric normed field `K : Type u`, an actual
`PresentedAffinoidAlgebra K` called A, a finite index type `I : Type v`,
and a family `D : I → RationalChart K A`. The universes u and v are
independent. A is a quotient of a finite weighted Tate algebra by a closed
ideal, with its constructed quotient norm. Every base polyradius is positive
and otherwise arbitrary. Each D(i) retains its own finite positive
polyradius, denominator, numerator tuple, and proof that their images
generate the unit ideal of A. Its algebra is the existing actual closed
rational quotient, and its structural map is the bounded homomorphism
`(D i).baseMap : BoundedAlgHom K A (D i).algebra`.

The covering hypothesis is
`∀ x : BanachSpectrum A, ∃ i, x ∈ (D i).locus`. It uses the original rational
inequality loci in the actual seminorm spectrum. For a section
`s i : (D i).algebra` on each member, compatibility means equality after
the two actual bounded restrictions to `(D i).inter (D j)` for every i,j.
This intersection is the published product presentation retaining the
denominator-extended numerator products and their product radii. Its locus
is exactly `(D i).locus ∩ (D j).locus`. The maps in the compatibility
equation are precisely `interLeft` and `interRight`, with their published
equations over A.

The conclusion is that there exists exactly one element `a : A` whose
image under every `(D i).baseMap` is `s i`. All compatibility and descent
equations concern actual algebra elements, including their nilpotent
information. They are not equations only after evaluation at spectrum
points. No output algebras, covering-refinement system, sheaf property,
exactness hypothesis, or gluing operator is supplied as an input.

This is scalar degree-zero descent: injectivity of the first map in the
augmented Cech complex gives uniqueness, and exactness at the first product
gives existence for a compatible family. The target retains arbitrary
positive real base and relative radii and complete trivially valued fields.
It imposes no reducedness, proper-ideal, nonempty-spectrum, or nonempty-index
condition. Empty coordinate tuples, zero quotient algebras, and empty
rational loci are allowed. For an empty I, the covering hypothesis forces
the base spectrum to be empty, and the conclusion requires A to have
exactly one element. This empty-cover case remains an obligation of the
future proof.

The mathematical source is Vladimir G. Berkovich, *Non-archimedean analytic
spaces*, Trieste lectures (2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1 and Exercise 2.2.2(ii)-(iii), printed/PDF p. 9, give the
affinoid-domain, rational-quotient and intersection setting. The single
input denominator g and the quotient relations `gT_i - f_i` fix the
interpretation of the exercise despite the displayed `g_i` and m/n
subscript inconsistencies. The Lean inputs use explicit unit generation;
no equivalence with the source's absence-of-common-zeros condition is
asserted here.

Fact 2.2.6(i), printed/PDF p. 10, asserts exactness and admissibility of the
augmented Cech complex for a finite affinoid covering and a finite Banach
module. Taking the scalar module M = A and keeping the first two
exactness assertions gives this target's mathematical provenance. The
explicit product-overlap presentation and the independent finite-index
universe are internal packaging in the existing quotient API. The original
pages and displayed formulas were read directly; no source-specific errata
note was present in the project literature and Library notes searched.

This also generalizes the published strict, unit-radius target
`Langlands.Analytic.StrictTestDomain.WholeSpectrumRationalGluingStatement`,
authored by Worker 101 with the target division specified by Worker 135.
Its proof does not supply arbitrary-radius descent by instantiation.
Higher Cech exactness, admissibility of the Banach-module maps, descent for
other finite modules, gluing over a chosen relative rational target,
categorical sheaf conversion, and the unrestricted analytic atlas and site
constructions remain separate obligations. No full Tate acyclicity theorem
or completion of those constructions is claimed by this statement.
