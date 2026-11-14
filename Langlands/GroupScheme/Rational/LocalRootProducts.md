# Integral ordered root products over a local base

This internal derived construction combines the actual field products in
`NonreductiveRootProducts`, the root-ray transport in
`LocalRootRayComparison`, and the fibrewise open-immersion criterion.
It concerns actual subgroup functors and scheme morphisms on all test
schemes. It is a supporting ingredient for integral-model generation,
not a proof of `UnramifiedParahoricModelStatement`.

## Arbitrary-base comparisons

For a map from the coordinate split torus indexed by a finite type `I`,
`exponentRoot_subgroup_baseChange` proves that the actual root subgroup
functor for a fixed integer exponent vector commutes with arbitrary
base change. The coordinate-torus base-change isomorphism is part of
the formula. The proof transports the base-changed character through
that isomorphism and applies the existing root-functor base-change theorem.

`exponentRoot_le_dynamicUnipotent` proves containment of this root
functor in the dynamic radical of a fixed-exponent cocharacter whenever
their integer dot product is strictly positive. The composition of the
character with the cocharacter is the corresponding positive power;
the existing positive-power contraction theorem gives the containment.
These two comparisons require neither a field nor a local base.

## Integral product chart

Let `R` be a commutative local ring, and let `G` be a smooth affine group
over `Spec R` with geometrically connected fibres. Supply a map `i` from
the coordinate split torus, a cocharacter exponent vector `ν`, and one
field `R`-algebra `k`. On that field fibre assume that distinct indivisible
positive actual roots have disjoint complete positive integral rays.
Supply an injective ordered enumeration of precisely those roots by
characters with fixed exponent vectors `m : Fin n → I → ℤ`.
Indivisibility is divisibility within the actual root set, as defined in
`RootProductStatement`.

Supply any integral representatives `j r : H r ⟶ G` of the actual root
functors with exponents `m r`, with each `H r` smooth. Supply any
representative `jU : U ⟶ G` of the actual dynamic radical of `ν`.
`orderedRootProductIso_localRing` constructs an isomorphism over `Spec R`
from the underlying scheme of the ordered finite product of the `H r`
to `U`. Its companion theorem
`orderedRootProductIso_localRing_hom_comp` states the exact equation:
the chart followed by `jU` equals ordered multiplication of the original
maps `j r`.

The construction retains arbitrary universe `u`, the supplied order,
and the empty product. It assumes neither reductivity of `G` nor
maximality or monomorphy of `i`. Ray disjointness remains an explicit
assumption on the one chosen field fibre. Smoothness and representability
of the integral root factors are also inputs.

## Implemented proof

`isIso_orderedRootProduct_fieldFibre` first transports the actual root
enumeration and ray disjointness from `k` to any field `R`-algebra `K`
using local-base weight-support constancy and coordinate-lattice
comparison. Geometric connectedness of `G` supplies connectedness of
this fibre. The arbitrary-base comparisons identify the base-changed
root and dynamic representatives. The field product theorem then gives
a chart on these exact representatives.

This lemma accepts factor maps from the `H r` into `U` whose composites
with `jU` are `j r`. Monomorphy of the represented dynamic subgroup
identifies their ordered multiplication with the field chart. Thus the
actual product map is an isomorphism on every field fibre.

`isIso_orderedRootProduct_localRing` proves that the same product map
is an isomorphism over `R`. The dynamic representative is smooth by
`dynamicRingSmoothConnected`; the finite product of the smooth factors
is smooth. Reindexing through `ULift (Fin n)` lets the smooth-product
theorem apply without restricting the base universe. For each point
of `Spec R`, the residue field is made an `R`-algebra through its actual
structure map. The product base-change comparison and the preceding
field lemma give an isomorphism on that residue-field fibre.

The private fibrewise helper applies the published open-immersion
criterion using flatness and local finite presentation of the source
and local finite type of the target. It proves surjectivity by lifting
each target point to the residue-field fibre over its image in the
base. An open immersion that is surjective is an isomorphism, and the
forgetful functor reflects this to schemes over the base.

Finally, `exists_orderedRootProductIso_localRing` derives positivity
of every exponent dot product from membership in the enumerated
positive-root set. Positive-power containment and the existing
represented-subgroup `inclusionHom` give the required integral factor
maps and their original ambient equations. The integral isomorphism
theorem applies to their ordered product. The named chart chooses this
isomorphism and retains its equation.
