# A representative formula for scalar cup in degree minus two

Let `G : Type u` be a finite group, `A : Type u` a commutative
multiplicative group with a distributive `G`-action, and `c` an actual
normalized two-cocycle with values in `A`. The scalar ring is
`ULift.{u} ℤ`, and all Tate groups are the actual Tate cohomology groups.
This internal unit computes scalar cup with the ordinary class
`cohomologyClass c` on the published single-chain class
`minusTwoClass (integralTrivial G) g 1`.

The augmentation ideal and splitting representation are those of
`CocycleSplittingModule`, `CocycleSplittingExtension`, and
`CocycleSplittingClass`. Write `delta(h)` for the coordinate vector at
`h` in the regular representation. The augmentation cocycle is
`e_g = delta(g⁻¹) - delta(1)`. Its norm is zero:
the inclusion of the ideal commutes with norm, and right translation
sends `delta(1)` to `delta(g⁻¹)`. Norm is unchanged by this translation,
so the norm of the difference vanishes. The proof uses injectivity
of the ideal inclusion.

`inverseRowSum c g` is the actual coefficient element
`∑ h : G, Additive.ofMul (c(h,g⁻¹))`. The norm of the splitting-module
element `(0,e_(g⁻¹))` is `(inverseRowSum c g,0)`. Its second component
vanishes by the preceding augmentation norm calculation. The first
component follows from `twist_augmentationCocycle`, which identifies
the correction term on `e_(g⁻¹)` with `Additive.ofMul (c(h,g⁻¹))`.
As the norm is invariant, its first component is invariant as well.
`inverseRowInvariant c g` packages this invariant coefficient element.

`scalarH2Cup_minusTwoClass` proves

```
scalarH2Cup (coefficientRepresentation G A) (-2) (cohomologyClass c)
    (minusTwoClass (integralTrivial G) g 1)
  = zeroClass (coefficientRepresentation G A) (inverseRowInvariant c g).
```

The proof replaces `cohomologyClass c` by the positive scalar double
boundary of the splitting and augmentation sequences, using
`scalarDoubleBoundaryClass_eq`. The scalar splittings allow
`scalarH2Cup_doubleBoundary` to identify cup with the composite of the
two actual Tate connecting maps. Apply `delta_minusTwoClass` to the
augmentation sequence, lifting coefficient one by `delta(1)`.
Mathlib's first-homology differential uses the inverse action,
so its coefficient difference is
`g⁻¹ · delta(1) - delta(1) = e_(g⁻¹)`.
The first connecting map therefore gives the norm-zero class of
`e_(g⁻¹)`. Lift that element to `(0,e_(g⁻¹))` in the splitting
representation and apply `delta_minusOneClass`; its computed norm
gives the displayed degree-zero class.

The provenance is internal: the formula follows from the published
coordinate actions, scalar double-boundary theorem, and actual-complex
representative formulas. There is no assumption of cup bijectivity or
any arithmetic reciprocity law. The inverse in the second cocycle
argument is part of the proved formula. Evaluating this sum for cyclic
carry cocycles and comparing local reciprocity conventions remain
separate obligations.
