# Actual source building and comparisons for the supplied derived cover

Let `F : Type u` be a nonarchimedean local field and
`P : ParahoricBuildingData G`. This module uses the actual derived subgroup
`P.zeroDatum.d : D → G` and simply connected cover
`P.zeroDatum.π : C → D` already stored in `P`. It constructs source valuation
data and the original root, action and normalizer comparisons for that same
cover.

The structural input consists of maximal split tori `j : T → D` and
`k : U → C`, a split torus `A`, morphisms `e : T → P.S`, `c : A → P.S`,
`f : U → T`, and the two original squares

```text
j ≫ d = e ≫ P.i
k ≫ π = f ≫ j.
```

The actual retained/central product of `e` and `c` is flat and surjective as
a scheme map, `c ≫ P.i` is central on every test scheme, and `f` is an
isogeny. The implementation also has explicit scheme-smoothness for `G`
and monomorphism typeclasses for `j` and `k`; these follow respectively
from `P.isConnectedReductive` and the supplied maximality proofs.
Affineness and smoothness of `D` and `C` are derived locally from the
semisimple and simply connected cover properties stored in `P`.

`derivedCoverApartment` first applies the literal derived valuation pullback
to `P.apartment`, then applies the literal central-isogeny pullback through
`π`. It is an actual `KPApartmentData k (localFieldOrder F)`, with the
original V0–V5 predicate, split-torus compatibility, full translation orbit
and stability under every source normalizer.

Given actual `CD : CentralizerDatum j` and `CC : CentralizerDatum k`,
`derivedCoverValuationBuildingData` constructs
`ValuationBuildingData C`. Its connected reductivity comes from the actual
simply connected cover. Its torus is `U`, its embedding is the original `k`,
its apartment is the constructed two-stage pullback, and its centralizer is
`CC`. The full V6 field is proved by first applying the actual derived
centralizer transfer to `P.isOmegaCompatible`, then applying the original
central-isogeny full V6 transfer. No source valuation, full V6 or source
apartment axiom is supplied as a premise.

`derivedCoverApartmentAffineEquiv` composes the original point affine
pullbacks, from the ambient apartment to the constructed cover apartment.
`derivedCoverNormalizerMap` composes the original forward normalizer maps
in the opposite direction. Its evaluation theorem identifies its value
with exactly `rationalPoints.map (π ≫ d) n`, and its action theorem
intertwines the two original apartment actions.

`transportedRoots_derivedCoverApartment` combines the exact derived and
central-isogeny affine-root comparisons. Inverse precomposition along a
composite affine equivalence equals the composite functional transports;
the two previously proved root-set equalities thus identify the original
source roots.

`exists_derivedCoverNormalizer_lift` supplies every target normalizer in
`P.simplyConnectedImage` with an actual source normalizer preimage. Membership
is in the original rational-point range of `π ≫ d`. The two torus squares
give the composite square, and the published
`DerivedCoverNormalizerLift.exists_normalizer_lift` proves that a chosen
cover point in that range normalizes the original maximal source torus.
The evaluation theorem for the constructed forward map identifies its
image with the target normalizer.

`derivedCoverSourceAffineEquiv` is the inverse point affine equivalence,
now with the constructed `ValuationBuildingData C` as its source.
Its action theorem and `transportedRoots_derivedCoverSource` prove the exact
equivariance and root comparison in the direction required by
`SimplyConnectedNormalizerCoverTransport`.

Finally, `normalizer_map_eq_affineWeylGroup_of_derivedCoverData` instantiates
that existing theorem with the constructed source, map, affine equivalence,
root identity, equivariance and actual normalizer lifts. It still explicitly
requires the exact simply connected facet-fixing statement, opposite-factor
pairs for the source and target, and the original target apartment axioms.
It assumes no full source apartment axioms or source AS5. This conditional
integration lemma is not a proof of the unchanged published
`SimplyConnectedNormalizerAffineWeylStatement`.

The construction is internal, combining the actual derived transfers with
the existing central-isogeny and normalizer transport results; no additional
external theorem is invoked. Existence of the structural tori/product and
both actual source centralizer data remains to be established, as do the
unconditional facet-fixing and opposite-factor-pair prerequisites. No such
premise is added to the final published target.
