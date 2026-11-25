# Differentials of simple-root scaling automorphisms

For every supplied `AffinePinnedModel M`, every tuple of simple-root units `c`, and every chosen simple root `a`, `rootScalingIso_rootVector` proves

```
Lie.targetMapLinear (M.rootScalingIso c).hom R (M.pinning a 1).val
  = (c a : R) • (M.pinning a 1).val.
```

`rootScalingAutomorphism c` packages the actual automorphism with its torus-fixing equality and all these simple-root differential equations in one subtype value.

Here `R` is `CommRingCat.of M.ring`. No reducedness, field, nonzero-ring, or rational-point-lifting hypothesis is imposed.

The proof first establishes two internal descent lemmas. Injective test-algebra maps reflect equality of actual Lie vectors, by the natural comparison with identity derivations. A base point of an affine fppf quotient lifts over a faithfully flat algebra: form the affine pullback along that point, express the pullback as the spectrum of an algebra, and use flatness and surjectivity to obtain faithful flatness.

For the scaling formula, lift the prescribed quotient-torus point along the simple-root projection. The coordinate lemmas identify its simple-root monomials with the images of the units `c a`. The restriction of the descended action is the original torus conjugation, so after coefficient extension its differential is the adjoint action. The defining all-test equation of the actual exponent weight space gives the claimed scalar on the extended pinning vector. Faithful flatness makes the coefficient map injective, and the first lemma reflects this equality to the original Lie module. Naturality of the actual target Lie map connects this calculation to the evaluated automorphism.

The mathematical provenance is the pinning-scaling argument of Brian Conrad, *Reductive group schemes* (2014), Corollary 6.1.15, pp.195–196. This module supplies an internal arbitrary-ring differential calculation for the quotient-torus construction in `AffinePinnedScalingAction`. It uses faithfully flat descent of equality rather than the field-only character weight decomposition.
