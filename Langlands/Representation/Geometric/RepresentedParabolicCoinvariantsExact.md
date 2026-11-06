# Exact image quotients for represented-parabolic coinvariants

This internal construction supplies the exactness step for normalized radical
coinvariants on representations of the parabolic itself. It supports the
passage from support quotients to coinvariant-image quotients in Renard,
*Représentations des groupes réductifs p-adiques*, 2026 version, VI.5.1,
printed pp.163–164 / PDF pp.169–170.

The actual functor is imported from `RepresentedParabolicCoinvariants`.
`continuous_leviToParabolicPoints` proves that the Levi point map into the
literal parabolic image is continuous. It is the existing Levi-point
homeomorphism followed by the continuous subgroup inclusion.

`isSmooth_leviParabolicCoinvariantsFunctor_obj` proves smoothness of
normalized coinvariants for every smooth representation of the parabolic.
The radical quotient has a smooth descended action, restriction along the
continuous Levi map preserves smoothness, and the inverse half character
has open kernel. `smoothLeviParabolicCoinvariantsFunctor` bundles these same
objects and the original quotient maps in the full smooth category.
Forgetting smoothness recovers the imported algebraic functor.
The zero-morphism law follows by evaluating each quotient map on vector
classes.

`smoothLeviParabolicCoinvariantsFunctor_exact` assumes
`IsLimitOfCompactSubgroups` for the actual radical viewed inside the
parabolic image. Under this explicit compact-containment premise the
published character-localization exactness theorem proves injectivity,
middle exactness and surjectivity for every short exact sequence of smooth
parabolic representations. Restriction of the descended action and scalar
twisting retain the underlying linear maps and thus these three properties.
This module does not derive the compact-containment premise from algebraic
unipotence.

`leviParabolicCoinvariantsImageQuotientIso` applies the existing generic
`RepSubfunctor.exactImageQuotientIso` to this proved exact functor. For any
smooth parabolic-valued functor and two nested actual subfunctors, its
source is the quotient of their actual mapped images. Its target is the
actual successive quotient followed by the normalized parabolic
coinvariant functor. The comparison is natural in the full input category
and uses the existing maps of subrepresentations and quotients.

The field, representation carrier and input category universes are
independent. No representation finiteness or admissibility hypothesis is
used. The output still needs to be matched with the particular ambient
support-image subfunctors, and the local normalized orbit comparison and
distinct-radical modulus cancellation remain separate obligations. The
closed geometric-lemma target and its hypotheses are unchanged.
