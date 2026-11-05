# Finite descent of additive polynomial points

This internal supporting module compares actual polynomial-valued points of a
group over a field with actual vector-group homomorphisms over an extension.
`IsAdditiveOver` is the universal additive identity with extension coefficients
and the original target group. Injective coefficient extension preserves and
reflects this identity, by polynomial substitution compatibility and injectivity
on points of an affine target.

The affine base-change equivalence identifies that identity with the published
`IsAdditive` predicate over the extension. `homOfAdditiveOver` therefore recovers
an actual vector-group homomorphism and its exact underlying polynomial point.
Evaluation at a base-field tuple times epsilon is the published actual input
tangent. Coefficient extension commutes with that evaluation, so a nonidentity
evaluated tangent cannot become the identity in a coefficient model.

For an affine target locally of finite type and a Galois coefficient extension,
`finiteGaloisHomModel` first chooses a finite Galois field of definition for
the underlying polynomial point. Reflection of additivity supplies an actual
homomorphism over that intermediate field. `FiniteGaloisHomModel` stores it
and the exact coefficient-extension equation. A nonzero input tangent in a
specified base-field coordinate direction remains nonzero for this model:
otherwise its epsilon evaluation, and hence the original evaluation, would
be the identity. No monomorphism assumption is made on the model.

Provenance: these are internal comparisons using the published affine base-change
equivalence, additive polynomial homomorphism construction, substitution
compatibility, and explicit dual-number algebra maps. No splitness result is
assumed or concluded here.
