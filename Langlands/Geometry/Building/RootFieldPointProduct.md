# Actual split-root products of root-field points

This is internal infrastructure for comparing actual root-field coordinates
with a root subgroup after passage to a splitting field. It derives its content
from the existing root-orbit Lie-line coordinates, the invariant weight-space
equivalence, and intrinsic root-point Lie naturality for field extension and
torus restriction. It makes no independent claim from the literature.

Work at arbitrary universe `u`. In the main constructions, `L/k` is a finite
Galois extension, `G` is a smooth affine connected reductive group over `k`,
`j : T → G` is a maximal torus, and `f : S → T` is a homomorphism from a split
torus. The torus `T` splits over `L`. The character `a` of `S` is nonzero and
has no higher positive roots for the action through `f` and `j`. A chosen
upper root `β` has Galois orbit equal to the complete fibre of roots restricting
to the scalar extension of `a`. No apartment, valuation, or integral-model
compatibility is supplied or concluded.

`HasNoHigherRoots.of_restriction` is a more general split-torus helper.
If the restriction of an upper character is a nonzero character with no higher
roots, the upper character also has no higher roots. A higher upper root
would restrict to a higher lower root; torsion-freeness of the split character
lattice ensures that this restricted multiple is nonzero. The helper does not
require reductivity or maximality.

`rootPointLieEquiv_congr` records equality of intrinsic ambient Lie vectors
when two acting homomorphisms are equal and the two actual root points have the
same ambient value. After substituting the homomorphism equality, subtype
extensionality identifies the points. This handles the propositional functor
composition identity in the main comparison.

`rootOrbitFieldPoint` sends an element of `rootOrbitField k L j β` to an
actual `k`-rational point of the root group for `a`. It uses the existing
root-field-to-weight-space additive equivalence and the inverse intrinsic
root-point Lie equivalence, then restores multiplicative notation.
`rootOrbitFieldPoint_extendedLie` proves that the extended point's intrinsic
Lie vector is the literal ambient vector given by the invariant orbit tuple.
The proof uses the actual field-extension square, cancels the inverse
equivalence, and applies the existing scalar-extension formula for the
root-field weight-space equivalence.

`rootOrbit_restriction` reads the restriction of every orbit root from the
orbit-fibre equality. `rootOrbit_hasNoHigherRoots` combines that equality
with preservation of the lower no-higher-root condition under field extension
and the restriction helper. `rootOrbitPointEquiv` then gives actual split
root points from `Multiplicative L` at each orbit root, using the coherent
Lie-line coordinate and the inverse intrinsic root-point Lie equivalence.
`rootOrbitPointEquiv_lie` proves that their intrinsic Lie coordinate is the
chosen coherent line coordinate by cancellation of the two equivalences.

`rootOrbitFieldPoint_fieldExtend_eq_product` states that extending the actual
root-field point equals the ordered product of those actual split root points,
evaluated at the conjugate embeddings of the root-field element. The equality
is of ambient `L`-rational group points. It holds for every finite enumeration
`Fin n ≃ orbit β`, without an additional chosen-product or compatibility premise.
The main hypotheses, in particular the absence of all higher positive roots,
remain in force.

For the proof, each upper factor belongs to the lower root group by the actual
torus-restriction inclusion. Thus the ordered product is a point of the same
lower root group as the scalar extension. The intrinsic lower point-to-Lie
equivalence sends the extension to the invariant root-field vector and sends
the product to the sum of the upper Lie vectors. The coordinate cancellation
lemma identifies each summand. The existing formula
`rootOrbitFieldFixedSpanEquiv_val`, reindexed through the chosen enumeration,
identifies the sum with the invariant vector. Injectivity of the intrinsic
equivalence proves equality of the actual ambient points.

This comparison has no depth parameters, integral models, special fibres, or
kernel geometry. It supplies a field-level prerequisite for the root-depth
problem; the supplied-apartment normalization and the full kernel statement
remain separate obligations.
