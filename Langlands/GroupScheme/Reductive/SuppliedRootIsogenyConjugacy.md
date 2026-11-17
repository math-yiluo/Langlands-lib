# Supplied-root torus conjugacy over arbitrary rings

This internal derived construction supplies whole-group torus conjugacy
from a common actual root-datum map over an arbitrary commutative ring `R`.
The two ambient homomorphisms are finite. Their source and target are
reductive affine group schemes with closed fibrewise maximal coordinate
tori and supplied finite reduced full fibrewise root data `P` and `Q`.
Both maps have the same coordinate torus map, compatible on every integral
exponent character with a supplied root-datum isogeny
`r : RootDatumIsogeny p Q P`.

`SuppliedRootIsogeny.TorusConjugacyLift` packages a cover of a parameter
scheme `V`, its projection and a point of the target coordinate torus,
the flatness, surjectivity and local finite presentation of the
projection, and the whole-group conjugation identity on every scheme
refining the cover.

The target roots corresponding under `r.indexEquiv.symm` to the source
simple roots are independent. Applying `r.weightMap` to an integral
relation gives a relation among the independent source simple roots,
with coefficients multiplied by the positive root factors. Each original
coefficient must therefore vanish. The existing supplied-root alignment
lift applies to these target characters and to the ratios of the two
maps' unit root coefficients.

`exists_fppf_torusConjugates` takes explicit freeness assumptions: every
actual source and target root
weight space is linearly isomorphic to `R`. The published global
root-parametrization construction chooses actual root maps from these
free weights. A chosen base of `P` and the independent target characters
above give an fppf cover of every `V` and a target torus point aligning
the two maps on these source simple roots.

The existing `TorusConjugates.of_simpleRootParametrizations` then proves
the whole-group equation on every source-group point over every scheme
refining the cover. That theorem constructs Weyl-normalized families
only on local coefficient tests to verify equality of the fixed
homomorphisms; no global normalized family is assumed here.

`suppliedRootConjugacyLift` chooses the resulting cover and torus point
as a `TorusConjugacyLift`, retaining the projection's three geometric
properties and the whole-group conjugation proof as fields.

`fppfLocallyTorusConjugate_of_supplied_rootDatum` applies this construction
to the terminal parameter scheme and packages the result as a singleton
fppf cover of the base. The common-root-datum adapter unpacks
`HasCommonRootDatumTorusMap`, retaining the two actual free-weight
assumptions.

There is no local-ring, nontriviality, reducedness, or decidable-equality
assumption on the base or coordinate types. The conclusions quantify over
all scheme tests, including nonreduced tests and the zero-ring case.
Ambient flatness and surjectivity are unnecessary for this supplied-data
construction.

The provenance is composition of the supplied-root alignment construction,
global root coordinates from free weights, the local-test rigidity
criterion, and the existing singleton-cover packaging. The linear
independence argument already appears in the local supplied-root
conjugacy construction and does not use a local ring. The existence of
compatible root data for an arbitrary isogeny and the general-base
affine-cover descent remain separate obligations; this module does not
assert the unconditional isogeny-torus rigidity theorem.
