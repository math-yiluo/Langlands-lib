# Adjoint automorphisms of the reduced and compact archimedean Lie algebras

Author: Worker 2. Namespace: `Langlands.Global.ArchimedeanGL`.

This module restricts the published matrix adjoint action to the actual reduced
real Lie algebra and to the compact real Lie algebra, then complexifies both
restrictions. Its parameters are `K : Type u`, `[Field K]`, and every natural
rank `n`, including zero. Thus it applies to number fields in arbitrary
universes, but its algebraic constructions need no `NumberField K` instance.

## Reduced algebra

`realTrace_realLieConjugation` proves that conjugation by any
`g : InfiniteAdelicGL K n` preserves `realTrace K n`. In matrix coordinates,
this is invariance of matrix trace under conjugation by a unit, followed by
the coordinatewise real-part map. Therefore conjugation preserves the
published kernel `reducedLieSubalgebra K n`, which imposes zero trace at real
places and zero real part of trace at complex places.

`reducedRealLieConjugation K n g` is the resulting real Lie equivalence of
that kernel. Its underlying map is precisely `realLieConjugation K n g`,
as recorded by `reducedRealLieConjugation_coe`; its inverse uses `g⁻¹`.
Addition, real scalar multiplication and the bracket are preserved by the
ambient map and the subtype inclusion.

`reducedComplexLieConjugation K n g` is its complex scalar extension on
`ReducedComplexLieAlgebra K n = ℂ ⊗[ℝ] reducedLieSubalgebra K n`.
The elementary-tensor formula is

`Ad_reduced,ℂ(g) (z ⊗ X) = z ⊗ Ad_reduced,ℝ(g) X`.

The underlying linear equivalence uses `LinearEquiv.baseChange`; its bracket
law is supplied by `LieAlgebra.ExtendScalars.map`. Tensor induction proves
`reducedComplexInclusion_conjugation`, saying that the published inclusion
intertwines this action with `complexLieConjugation K n g` on the full complex
Lie algebra.

## Compact algebra

For every `k : standardInfiniteCompact K n`,
`standardCompact_coordinates_star` proves that the star of its mixed matrix
coordinates is its inverse. The proof takes a preimage under the published
compact-factor map and checks the coordinates of its real orthogonal and
complex unitary factors. The compact group is the full published subgroup;
no restriction to its identity component is made.

Using product reversal by star and the preceding inverse identity,
`realLieConjugation_star` proves

`Ad(k) (star X) = star (Ad(k) X)`.

Consequently conjugation preserves the equation `star X = -X` defining
`compactLieSubalgebra K n`, as proved by
`realLieConjugation_mem_compact`. `compactRealLieConjugation K n k` restricts
the ambient real Lie equivalence to that subalgebra; its inverse uses `k⁻¹`.
Its coercion formula identifies the underlying matrix conjugation.

`compactComplexLieConjugation K n k` complexifies this restriction on
`CompactComplexLieAlgebra K n = ℂ ⊗[ℝ] compactLieSubalgebra K n`.
Its elementary-tensor formula keeps the complex coefficient fixed.
`compactComplexInclusion_conjugation` proves compatibility with the ambient
complex adjoint action by tensor induction.

## Action laws and the relative inclusion

For each of the four prefixes `reducedRealLieConjugation`,
`reducedComplexLieConjugation`, `compactRealLieConjugation`, and
`compactComplexLieConjugation`, the module proves:

- `_one`: the map of the identity is the identity equivalence.
- `_mul`: the map of `g * h` is `(map h).trans (map g)`, hence applies `h`
  first and `g` second.
- `_inv`: the map of the inverse is the inverse equivalence.

The real laws follow from the ambient laws through subtype extensionality.
The complex identity and product laws follow through the injective complex
inclusions. The complex inverse laws follow from the product and identity laws.

`compactToReducedComplex_conjugation` proves that the existing inclusion of
the compact complex algebra into the reduced complex algebra intertwines
their compact actions. Applying the injective reduced inclusion reduces the
claim to the two ambient compatibility identities and
`reducedComplexInclusion_compact`. Thus the action on the actual relative pair
is compatible with both published ambient inclusions.

## Internal provenance and scope

These constructions are internal consequences of the published
`ArchimedeanAdjoint`, `ArchimedeanSplitCenter`, `ArchimedeanCompactLieAlgebra`,
and `ArchimedeanCompact` definitions. Mathlib's `Matrix.trace_units_conj`,
star identities, scalar extension and Lie equivalence APIs supply the
algebraic ingredients. No adjoint action or preservation certificate is an
input, and no new correspondence with an original-literature assertion is
claimed.

The real trace condition precedes complexification, so the construction
retains the imaginary scalar directions at complex places. No positive-rank
assumption is needed. The unit supplies algebraic automorphisms and their
compatibilities; it does not identify the compact algebra with a group tangent
space, differentiate a compact representation, or construct relative cochains
or cohomology. Those remain separate constructions and theorem obligations.
