# Conjugated torus and splitting-field transport

This internal helper transports splitting over a compatible square of field
isomorphisms using the two tower base-change isomorphisms. It also transports
a maximally split maximal torus under a field isomorphism and an ambient
group isomorphism.

For a local field, choose a normal lift of an automorphism of its maximal
unramified extension to the fixed separable closure. Its image of the given
intermediate field is finite Galois when the original field is. Restricting
the lift gives a compatible field equivalence, and spectral-norm invariance
shows equality of the prescribed intermediate-field valuations.

These are derived constructions from the Library torus transport and tower
comparison theorems and Mathlib normal lifts and spectral-norm invariance.
Construction of the conjugated zero datum and proof of subgroup stability
remain unfinished.
