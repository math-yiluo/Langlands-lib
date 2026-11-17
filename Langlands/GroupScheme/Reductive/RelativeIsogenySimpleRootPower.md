# Simple-root power formulas for finite maps with supplied root data

This internal derived module combines actual finite root restrictions from
`RelativeIsogenyRootUnit`, reflection compatibility from
`RootDatumIsogenyReflections`, and conditional homomorphism rigidity from
`LocalSimpleRootPowerRigidity`. The root-datum isogeny and its compatibility
with the actual torus map remain supplied hypotheses.

`OppositePower.HasPowerFormula.coefficient_eq_of_maps_eq` compares two power
formulas in the same source and target coordinates. If the actual root
restrictions agree and the target coordinate map is a root parametrization,
their coefficients agree. The degrees may differ. The proof evaluates the
formulas at the scalar point one, uses injectivity of the actual target root
parametrization, and identifies global sections over the base spectrum with
the base ring. This lemma works over any commutative ring.

`RelativeIsogeny.HasSimpleRootRestrictionFormulas r b u v phi` asserts the
existence of positive unit coefficients and negative scalar coefficients
satisfying `HasSimpleRootPowerFormulas`. Its root index map is
`r.indexEquiv.symm`, and its degree at the source root `a` is
`r.rootFactor (r.indexEquiv.symm a)`. Here `r` maps the target root datum to the
source root datum, as the character map is contravariant.

`hasSimpleRootRestrictionFormulas` proves this proposition over an arbitrary
local commutative ring, with affine source and target groups, supplied finite
reduced fibrewise root data, a supplied compatible torus map, and a finite
ambient homomorphism. The target is reductive and its torus is fibrewise
maximal. Actual parametrizations of all source simple roots and their
negatives, and of the corresponding target roots, are required. Source
reductivity and Weyl normalization are not needed for this construction.

The proof takes the previously constructed unit coefficient at each actual
restriction. Reflection compatibility identifies the source of the
negative restriction and gives equality of its degree with the positive
degree. Coefficients outside the supplied simple support are filled with
one and zero, since the formula predicate imposes no condition there. The
formulas hold on every scheme test, including nonreduced tests.

`hom_ext_of_simpleRootRestrictions` considers two finite homomorphisms with
the same supplied root-datum isogeny and actual torus map. It additionally
requires source reductivity, closed fibrewise maximal tori on both sides,
and a supplied source family whose simple Weyl points realize the simple
reflections. Equality of the positive simple-root restrictions then implies
equality of the ambient homomorphisms. The proof constructs both formula
families, identifies their positive coefficients using the comparison at
one, and applies `hom_ext_of_simpleRootPowerFormulas`; positivity of every
degree follows from the root-datum isogeny.

These results do not construct the supplied root-datum isogeny or a torus
conjugator. They discharge the actual power-formula and opposite-degree
inputs to local homomorphism equality, without a reducedness assumption on
the base ring.
