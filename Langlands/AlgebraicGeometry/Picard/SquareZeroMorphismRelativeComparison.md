# Picard obstruction naturality and relative cohomology comparison

Author: Worker 217.

This is an internal specialization and reduction between the actual
cohomology constructions. Its provenance is the imported definitions and
the proved unit-sequence and Picard-obstruction naturality in
`SquareZeroMorphismObstructionNaturality`.

For a morphism `f : X' → X` over `Spec R`, morphisms `i : Y → X` and
`i' : Y' → X'`, and a module arrow
`k : kernelModule i → f_* (kernelModule i')`,
`relativeIdealCohomologyMap f i i' k n` is the additive homomorphism

```text
Hⁿ(X, I) → Hⁿ(X', f^*I) → Hⁿ(X', I').
```

The first arrow is the existing `relativeCohomologyPullback`, and the
second is the map of `relativeCohomology` induced by the adjoint of `k`
under the specified module pullback/direct-image adjunction. The groups
retain their relative scalar actions along `X.hom` and `X'.hom`.
Defining this map requires no closed-immersion, square-zero, compactness
or compatibility hypotheses.

`idealCohomologyMap_relative` assumes
`RelativeAbelianSheafCohomologyPullbackStatement`. For every natural
degree and every actual ideal-cohomology class, it identifies the
Ext-defined `idealCohomologyMap` with `relativeIdealCohomologyMap` under
the existing relative additive equivalences. The proof applies the
assumed comparison to the two actual ideal modules and the inverse
absolute additive comparison, then cancels that comparison with its
inverse. It constructs neither a new comparison nor a replacement
cohomology pullback.

`squareZeroObstructionMorphismNaturality_of_relativeComparison` proves
the implication from that comparison statement to
`SquareZeroObstructionMorphismNaturalityStatement`. For the full
commuting square, square-zero immersions and compatible ideal arrow
specified by the target, the proof first rewrites the actual Picard
obstruction using `obstructionMap_naturality`, then applies the preceding
degree-two ideal comparison.

This theorem is conditional on the displayed relative comparison. It
does not prove that comparison or the unconditional host target. The
target's extra compactness assumptions on the ambient schemes are
retained by the implication, although the unit-sequence result uses
only compactness of the two closed subschemes.
