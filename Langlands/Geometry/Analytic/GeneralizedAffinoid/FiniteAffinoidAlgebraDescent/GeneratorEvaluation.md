# Local admissible evaluation quotients from global matching generators

This internal construction supplies the local evaluation quotients used in
the global-generation reduction for finite Banach affinoid algebra descent.
Its input is any finite tuple `s` in the actual complete matching algebra
whose projections generate each original local algebra over its original
base-domain algebra. The coefficient field, polyradii, full-domain cover,
local algebras, norms, and original transition maps are retained.

`algebra` adjoins one weighted variable for each matching generator to the
original presented base, with radius `‖s k‖ + 1`. `globalEvaluation` is the
actual bounded map sending these coordinates to `s`, constructed using the
finite Banach presentation module's evaluation machinery. It exists before
any assertion of surjectivity or admissibility. The coefficient triangle
`globalEvaluation_baseMap` retains the original matching structural map.

`cover` is the actual inverse-image finite full-domain cover of this weighted
presentation. Every member is the original affinoid pushout of the weighted
base map with the corresponding original domain's structural map. The
coefficient leg `coefficientMap` is the original second quotient leg.
`localEvaluation` is the bounded pushout lift of the global matching
projection and the original local structural map. Its two leg equations
hold for entire maps. The base-changed new coordinates map to the original
projections of the matching generators.

The elementary theorem `BoundedAlgHom.exists_coefficientMap_bound` bounds any
actual finite coefficient map directly, by the bound of its coefficient
homomorphism times a finite sum of generator norms plus one. It does not
infer boundedness from continuity over a trivially valued field.

`localEvaluation_isAdmissibleEpi` first uses the supplied finite Banach
structure on the local algebra to obtain controlled coefficients for the
projected generating tuple. The local polynomial with those coefficients
is formed by the coefficient leg and the base-changed coordinate tuple.
Its evaluation is exactly the prescribed coefficient sum. Combining the
two positive bounds gives controlled preimages for the actual evaluation
map, hence admissibility. `kernel` is its actual closed kernel.
`localQuotientEquiv` uses admissibility to identify the presented closed
quotient with the original local algebra, retaining bounds in both
directions.

The provenance is the composition of the published full-domain pullback,
bounded affinoid pushout, weighted-adjunction, and admissible closed-quotient
constructions with explicit finite Banach coefficient bounds. It is a
local step toward the derived finite-algebra descent formulation associated
with Kiehl's theorem. This module does not prove compatibility or effectiveness
of the local kernel family, global finite Banach coefficient descent, or
surjectivity of the global evaluation map. Empty finite tuples and empty
covers are allowed; no nontrivial valuation, strict-radius, or spectral
injectivity premise on a finite map is introduced.
