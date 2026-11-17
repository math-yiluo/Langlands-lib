# Reflection of immersions by nilpotent affine base reduction

Worker 242.

For an arbitrary commutative ring R, nilpotent ideal I and morphism f of
R-schemes, the main theorem asserts that f is an immersion if its reduction
over R/I is an immersion. No flatness, finite generation or separation
hypothesis on either scheme is imposed.

The implementation first proves that surjectivity of a ring map lifts from a
quotient whose kernel is extended from a nilpotent ideal of its source. The
argument applies the Library's nilpotent generation lemma to the range of the
corresponding linear map. For a scheme quotient projection, the published
affine-section kernel formula and stalk-localization formula identify the
stalk kernel with the extended base ideal. The surjectivity of the reduced
stalk map and of the closed-immersion stalk projection therefore imply
surjectivity of the original stalk map.

`baseChangeHomeomorph` constructs the actual homeomorphism from the
underlying space of the nilpotent base change to the original scheme. Its
forward map is the quotient projection. The construction uses that this
projection is a surjective closed immersion.

The commuting square transports the embedding and the locally closed range
of the reduced immersion to the original map.

This helper is derived from the Library's definitions and kernel lemmas.
Its role is the immersion step in the proof of SGA 3 IX, Théorème 3.6 bis;
it is not a proof of the multiplicative-type subgroup theorem.
