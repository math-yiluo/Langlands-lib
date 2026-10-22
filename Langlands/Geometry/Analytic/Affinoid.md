# Presented strict affinoid algebras

Author: Worker 36.

An object consists of a finite number of variables and a closed ideal in the
actual strict Tate algebra. Its carrier is constructed as the ring quotient,
with Mathlib's quotient norm, normed algebra structure and completeness. It is
not a record containing an unspecified Banach algebra with assumed analytic
properties. The quotient map is bounded and surjective, and each quotient
element has a representative whose norm is within any prescribed positive
amount of the quotient norm. The zero ideal supplies closed unit polydiscs.
The quotient norm is proved ultrametric by taking representatives within a
positive epsilon of each quotient norm, applying the Tate algebra's
ultrametric inequality, and then removing epsilon.

Morphisms are actual algebra homomorphisms with a positive linear norm bound.
Identity, composition and the category laws are proved directly. The category
of presented affinoid spaces is the opposite category. Its underlying space
functor takes the multiplicative spectrum of the quotient Banach algebra, and
maps act by composition of seminorms. Thus the categorical interface is tied
to the constructed algebras and spectra.

This uses a chosen quotient norm and presentation. Comparison with all
equivalent Banach norms and independence of presentations are subsequent
results. Only strict affinoids are covered; arbitrary polyradii, affinoid
localizations, a structure sheaf, analytic atlases and analytic sites have not
yet been constructed. Closedness of an input ideal is a hypothesis on that
actual ideal; the theorem that every ideal of a finite Tate algebra is closed
is not assumed here.

Original-source correspondence: Berkovich, *Non-archimedean analytic spaces*,
Trieste lectures (2009), Definitions 2.1.1 and 2.1.2, p. 7, and Definition
2.1.11, p. 8, at
https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf.
The quotient topology makes the presentation admissible in the sense of
Definition 2.1.1. The registered original is `berkovich-2009-trieste-analytic-spaces`,
SHA256 `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The source defines affinoid algebras up to admissible epimorphisms; this
implementation chooses an actual closed-ideal quotient and its quotient norm.
The algebra construction also permits incomplete coefficient fields; its
Banach-ring and topological-spectrum functors require `CompleteSpace K`.
This extension is explicit and is not asserted to be the source's Banach
affinoid category over an incomplete field.

The construction imports TateAlgebra, Spectrum.Definitions and Mathlib's
`Analysis.Normed.Group.Quotient`. The quotient's ring and norm instances,
bounded presentation map, opposite category and spectrum functor are
constructed directly; the accompanying lemmas verify those constructions.
