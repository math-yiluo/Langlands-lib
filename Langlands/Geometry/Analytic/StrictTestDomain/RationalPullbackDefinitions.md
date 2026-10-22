# Pullback of rational data along bounded algebra maps

Author: Worker 36.

For rational data `d` on a presented strict affinoid algebra P and an actual
bounded K-algebra map φ from P to Q, `d.pullback φ` has the same finite arity
and has denominator φ(g) and numerators φ(f_j). Its absence-of-common-zeros
condition is proved: a spectrum point x of Q pulls back to the spectrum point
`BanachSpectrum.comap φ.toBoundedRingHom x` of P, where the original condition
applies. Thus the constructor takes no additional nonvanishing assumption.

The projection lemmas identify these actual elements. `pullback_id` and
`pullback_comp` prove equality of rational data for identity and successive
bounded maps, including the proof field by proof irrelevance.
`locus_pullback` identifies the new rational locus with the inverse image
of the original locus under the actual spectrum map M(Q) → M(P).
`mem_locus_pullback` gives the pointwise version. Finally,
`hasImageIn_pullback_iff` says that a bounded map ψ from Q to a presented
strict affinoid R has spectrum image in the new locus exactly when ψ ∘ φ
has spectrum image in the original locus. These equalities follow directly
from the definitions: evaluation of a pulled-back seminorm at a is x(φ(a)).

Over a complete coefficient field, the existing `RationalData.algebra`,
`baseMap`, and `spectrumMap` constructors also apply to the resulting data,
yielding its actual closed-ideal Tate
quotient over Q and its structural maps. This module does not construct a
comparison map between the two rational quotient algebras or prove their
bounded pushout property. Nor does it prove that the pulled-back quotient
represents the inverse image; that requires the separate rational
representation theorem.

The construction and equalities need only an ultrametric normed coefficient
field; completeness is unnecessary for pulling back the data and inequalities.
For the intended complete coefficient fields, the algebras are presented
strict affinoids in the coefficient universe, and all rational radii are one.
Empty numerator tuples, zero and nonreduced algebras, and trivial scalar
valuations are permitted. The construction neither imposes spectral
injectivity nor assumes that a spectrum is nonempty.

This is a derived construction from Berkovich, *Non-archimedean analytic
spaces*, Trieste lectures (2009), Definition 2.1.11, printed/PDF p. 8, and
Definition 2.2.1 and Exercise 2.2.2(ii), printed/PDF p. 9. The source is
registered as `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The map direction comes from the opposite bounded-algebra category, and the
rational elements and their no-common-zero condition come from the exercise.
Mapping those elements and evaluating pulled-back seminorms gives the
construction and equalities above; they are not separately quoted source
theorems. This unit-radius construction does not assert the source's full
affinoid-domain property, which tests all affinoids, or a comparison with
relative power-series presentations.
