# Proof of bounded extension for the Weierstrass presentation

Author: Worker 36.

`WeierstrassPresentation.boundedExtension` proves the separate
`BoundedExtensionStatement`. The quotient, old-variable inclusion, base map,
coordinate equations, and norm locus are imported from Definitions.
The original module path retains the extension constructors for downstream
spectrum and localization constructions.

Every spectrum point maps into the indicated locus: the imposed equation
identifies each constrained base element with a new coordinate. The spectrum
seminorm is bounded by its quotient norm, which is at most the Tate norm one
of that variable. This proves the forward inclusion.

For a bounded base map, `solutionTuple` appends the images of the constrained
elements to the images of the old coordinates. The old entries have bounded
monomials by the Tate universal property. Explicit power bounds for the
finitely many added entries, together with the finite comparison between
power and monomial bounds, prove `solutionTuple_bounded`.

`evaluate_included` uses coordinate uniqueness for bounded maps from the old
Tate algebra to identify evaluation on included series with the original
base map. The old relations therefore vanish. Each new relation vanishes
because its new coordinate is assigned precisely the corresponding base
image. `liftFromBase` applies the relation-quotient lift to this evaluation.
Its composite with the base map agrees with the original map on quotient
representatives, hence everywhere by surjectivity.

For uniqueness, two maps agreeing on the base agree on the old coordinates
by the base-map formula and on the new coordinates by their imposed
equations. Coordinate uniqueness for the relation quotient identifies the
maps. This argument requires no completeness or ultrametric norm on the
target. The constructed lift and this uniqueness prove
`existsUnique_extension`; the closing theorem assembles the three clauses.

The Definitions and Statement Markdown explain the source conventions and
derived scope. This proof retains explicit power bounds for existence.
It does not establish reverse spectrum inclusion or infer those bounds from
spectral inequalities, and makes no analytic-domain or sheaf assertion.
