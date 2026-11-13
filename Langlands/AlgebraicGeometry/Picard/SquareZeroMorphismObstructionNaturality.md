# Square-zero unit boundaries under a morphism of thickenings

This is an internal compatibility result for the actual unit sequences of
square-zero closed immersions. Its provenance is the published constructions
of the unit sequence and Picard classifier, combined with the Ext-defined
pullback, its composition law and its connecting-map naturality.

Let `f : X' → X`, `i : Y → X`, `i' : Y' → X'`, and `g : Y' → Y` be scheme
morphisms in one universe, with `i' ≫ f = g ≫ i`. The definition
`sequenceQuotientMap` applies the actual unit reduction along `g` inside
the direct image along `i`, then transports the target along that equality.
It requires no immersion hypothesis.

Suppose `i` and `i'` are closed immersions whose actual ideal sheaves have
square zero. Let `k : kernelModule i → f_* (kernelModule i')` be a module
morphism compatible with the inclusions into the structure modules:
`k ≫ f_*(kernelModuleι i') = kernelModuleι i ≫ unitToPushforwardUnit f`.
The definition `unitSequenceMap` is a morphism from the actual square-zero
unit sequence for `i` to the direct image of the sequence for `i'`. Its
components are the underlying additive-sheaf map of `k`, actual structure-unit
reduction along `f`, and `sequenceQuotientMap`.

The kernel square is proved on sections: the compatibility of `k` with the
ideal inclusions says that its underlying value is the structure map applied
to the original value. Preservation of one and addition then identifies
the two images of `1+a`. The quotient square follows from composition of
the actual unit reductions and transport along the commuting-square equality.

The lemma `quotientCohomologyComparison` identifies the quotient arrow on
cohomology in every natural degree. After the existing homeomorphism
comparisons for the nilpotent immersions, it equals the actual unit-sheaf
cohomology pullback along `g`. The proof uses the all-degree composition law
for the Ext-defined pullback twice, transports along the square, and uses
its agreement with the existing cohomology equivalences for homeomorphisms.

The definition `idealCohomologyMap` conjugates the Ext-defined map with
coefficient `k` by the actual additive-sheaf/module-cohomology comparisons.
The lemma `boundaryMap_naturality` proves, for every degree `n` and every
unit-cohomology class `y` on `Y`,

```text
boundaryMap i' hi' n (cohomologyMap g n y)
  = idealCohomologyMap f i i' k (n+1) (boundaryMap i hi n y).
```

This follows from connecting-map naturality for `unitSequenceMap` and the
quotient comparison. No exactness of direct image along `f` is assumed.

When `Y` and `Y'` are compact, `obstructionMap_naturality` identifies the
actual Picard obstruction of `g^*y` with `idealCohomologyMap` applied to the
obstruction of `y`. The proof specializes boundary naturality to degree one
and uses the actual Picard/unit-H¹ classifier's naturality for arbitrary
scheme morphisms. No compactness hypothesis on `X` or `X'` is needed here.

These results use the actual ideal modules and cohomology groups. They do
not identify `idealCohomologyMap` with the relative module-cohomology
pullback followed by the adjoint of `k`. That comparison remains a separate
obligation in `SquareZeroObstructionMorphismNaturalityStatement`; this
module does not claim to prove that full target.
