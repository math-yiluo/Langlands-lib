# Absolute-value and curve-place completion comparison

For every nontrivial real absolute value `a` of a global function field `F`
over a finite field `k`, this module constructs a ring equivalence and a
homeomorphism

```text
a.val.Completion ≃+*
  (functionFieldPlaceOfAbsoluteValue k F a).heightOneSpectrum.adicCompletion F
```

and proves that the equivalence extends the identity on `F`. It identifies
the norm unit ball in the actual absolute-value completion with the existing
adic completion's valuation ring. The restricted equivalence is also a
homeomorphism for the subspace topologies.

## Provenance and assumptions

This is derived comparison infrastructure. Conrad's *Weil and Grothendieck
approaches to adelic points* (2011), printed p.1 and pp.6–7, uses actual
global-field places and their completed local factors. The module provides
an implementation-specific comparison for the function-field factors; it is
not attributed as a separate statement of that paper.

The place and valuation comparison comes from the published
`Langlands.Global.FunctionFieldAbsoluteValuePlaces`. The completion
construction uses pinned Mathlib's `WithAbs`, `WithVal`,
`UniformSpace.Completion.mapRingEquiv` and
`HeightOneSpectrum.adicCompletion.equiv`. The equivalent-valuation unit-ball
comparison reuses `Valuation.IsEquiv.valuedCompletion_le_one_iff`.

The generic absolute-value section assumes only a field `F`, a real absolute
value `a`, and a proof `ha : IsNonarchimedean a`. Its nontriviality is not
needed there. The generic equivalent-valuation section permits different
linearly ordered commutative value groups with zero on the same field.
The function-field section assumes fields `k` and `F` in the same arbitrary
universe, `Algebra k F`, `Finite k`, the specified `Algebra (RatFunc k) F`,
the compatible scalar tower, and `FunctionField k F`. The latter is the
finite-dimensional extension condition. No separability or normalization
premise is added. The required nonarchimedean inequality is proved by the
imported finite-constant theorem, rather than imposed on the representatives.

## Absolute-value and associated valuation completions

`absoluteValueWithValRingEquiv a ha` is the identity of the underlying field
between `WithAbs a` and `WithVal (absoluteValueValuation a ha)`.
`absoluteValueWithValUniformEquiv` proves that it is uniform in both
directions. The proof temporarily gives `F` the norm defined by `a` and its
ultrametric and valued-field instances. The resulting valuation is literally
`absoluteValueValuation a ha`. Mathlib's `WithVal.uniformEquiv` compares
that valued field with its `WithVal` copy. The identity between `WithAbs a`
and the normed `F` is an isometry in both directions. Composing these
comparisons proves the uniform equivalence.

`absoluteValueValuationCompletionEquiv` applies Mathlib's completion ring
equivalence construction to these maps. The two continuity theorems and
`absoluteValueValuationCompletionHomeomorph` use the actual completion
topologies. The formula
`absoluteValueValuationCompletionEquiv_coe` says that the canonical image of
`x : F` in the absolute-value completion maps to its canonical image in the
valuation completion. It follows from `Completion.map_coe` and uniform
continuity of the original identity comparison.

`absoluteValueCompletion_norm_add_le_max` extends the strong triangle
inequality to the completion by two-variable completion induction: the
inequality is closed by continuity, and on the dense original field it is
`ha`. This gives an ultrametric instance on the completion.

`absoluteValueValuationCompletionEquiv_le_one_iff` proves

```text
‖x‖ ≤ 1 ↔ Valued.v (absoluteValueValuationCompletionEquiv a ha x) ≤ 1.
```

Both unit balls are clopen. The absolute-value ball is an ultrametric closed
ball of positive radius, and the valued-field ball is its valuation ring.
The homeomorphism therefore makes the locus where these two membership
predicates agree closed. Completion induction reduces their agreement to
the original field, where the valuation is the nonnegative-real absolute
value and the equivalence is the identity.

`absoluteValueCompletionIntegers a ha` is the inverse image valuation subring
of the completed associated valuation along the ring equivalence.
`mem_absoluteValueCompletionIntegers` proves that membership is exactly
`‖x‖ ≤ 1`. Thus the type carries the existing subspace topology of that
literal norm unit ball; the topology is not transported from an auxiliary
target.

## Equivalent valuations and the curve-place completion

`equivalentValuationCompletionRingEquiv h` extends the identity between the
two `WithVal` copies when `h : v.IsEquiv w`. The uniform equivalence supplied
by `h` makes the extension continuous with continuous inverse. Its
`_coe` theorem proves identity on the original field, and its
`_le_one_iff` theorem applies Mathlib's completed valuation-ring comparison.

`functionFieldAbsoluteValueCompletionEquiv k F a` composes three maps:

1. The actual absolute-value completion to the completion of its
   nonnegative-real valuation.
2. The identity comparison to the completion of the corresponding curve
   place's discrete adic valuation, using the published
   `functionFieldAbsoluteValueValuation_isEquiv_adicValuation`.
3. The inverse of Mathlib's
   `HeightOneSpectrum.adicCompletion.equiv`, giving the actual existing
   adic completion type.

The two continuity theorems compose the corresponding continuity results.
`functionFieldAbsoluteValueCompletionHomeomorph` packages them without
changing either topology.
`functionFieldAbsoluteValueCompletionEquiv_coe` proves explicitly that
the canonical absolute-value image of `x : F` maps to `algebraMap F _ x`.
The proof applies extensionality into the underlying valuation completion
and uses the two preceding original-field formulas.

`functionFieldAbsoluteValueCompletionEquiv_mem_integers_iff` identifies
membership in the target's `adicCompletionIntegers F` with `‖x‖ ≤ 1`.
The proof successively applies the completed equivalent-valuation
comparison and the absolute-value unit-ball comparison.
`functionFieldAbsoluteValueCompletionIntegersEquiv` uses `RingEquiv.restrict`
and this membership equivalence to restrict the ring equivalence.
Its coercion theorem identifies its underlying map with the completed-field
map. The final
`functionFieldAbsoluteValueCompletionIntegersHomeomorph` proves continuity
in both directions by restricting the continuous completed-field maps to
their subtypes.

## Scope

This module compares all nontrivial real absolute-value completions with
their actual corresponding curve-place completions, including the integral
subrings and their topologies. It does not yet construct a restricted-product
comparison, establish local compactness or full diagonal discreteness, or
compare scheme-valued and algebraic-space-valued adelic points. Those remain
separate obligations of the encompassing five-section program.
