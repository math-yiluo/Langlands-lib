# Detecting the scalar commutant by a principal-series coefficient

Suppose a standard module is the quotient of a source by a surjective
intertwiner and embeds in a target by an injective intertwiner. Sandwiching an
endomorphism between the two maps gives a linear injection from endomorphisms
of the standard module to maps from the source to the target. The injection
sends simultaneous compact and Lie intertwiners to simultaneous compact and
Lie intertwiners.

A linear functional detecting every nonzero such map is consequently
injective on the endomorphism space. The proof evaluates it on the identity.
When this value is zero, the identity map is zero. Otherwise, dividing the
value on an endomorphism by the value on the identity gives its scalar.

The internal specialization `coefficientDetector` evaluates the coefficient
functional of `RealBottomMinorJacquet` on a fixed column configuration and a
fixed vector of the multiplier source. It supplies the linear functional
for this argument.
