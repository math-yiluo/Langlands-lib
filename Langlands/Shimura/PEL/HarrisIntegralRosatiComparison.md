# Actual comparisons for integral Harris Rosati equations

This internal construction uses the published contravariant composition and
identity laws for actual dual abelian-scheme maps. It assumes the displayed
chosen dual schemes, inverse line bundles with evaluation isomorphisms, and
dual geometry. It supplies no new dual-existence theorem.

For an actual isomorphism `c : B' ≅ B`, the transported actual map to the
chosen dual is `c.hom ≫ lam ≫ dual(c.hom)`. Dualization of `c.hom` is itself
an actual isomorphism: dualization of `c.inv` is its inverse by the
contravariant composition and identity laws. This is the existing constructor
`Langlands.AbelianScheme.dualAbelianSchemeIsoFromEvaluation` from
`DualAbelianBaseChangeCoherence`, reused with the two families in the required order.

If actual integral Harris-order actions on `B'` and `B` intertwine through
`c.hom`, dual functoriality gives the reversed dual intertwining square.
For each order element, the Rosati equation on `B'` is obtained by composing
the equation on `B` with `c.hom` and `dual(c.hom)`. These are isomorphisms,
so cancellation proves an equivalence of the equations. Quantification gives
the equivalence both for the finite Harris integer basis and for the entire
positive auxiliary order. Actual dual additivity is not needed for these
equivalences.

For a morphism `f : T' ⟶ T` over the original base, the second section
specializes this transport to `relativeBaseChangeComparisonIso B f`.
Its source is the direct pullback along `T'.hom`; its target is the
successive pullback along `f.left` of the family over `T`. The supplied
action over `T` has ordinary pullback action on the successive family and
canonical relative restriction on the direct family. The published
`relativeEndRestrict_comparison_intertwines` proves the required integral
equivariance for every order element.

`relativeIntegralRosatiComparisonMap` transports an actual map from the
successive family to its chosen dual. The theorems
`integralRosatiBasisEquations_relativeComparison_iff` and
`integralRosatiEquations_relativeComparison_iff` identify, respectively,
the finite basis equations and all-order equations on that family with
the equations for its transported map and relatively restricted action
on the original direct pullback. Both chosen duals and their displayed
geometry and evaluation data remain explicit. No finiteness or
noetherian hypothesis on the test schemes is required.

This is transport of the supplied actual map. No assertion that it is a
polarization, or that it equals a separately specified pullback
polarization, is included. The complete normalized CM representation,
ordinary moduli existence, rational-isogeny comparison, level structures,
and geometric existence results remain separate obligations.
