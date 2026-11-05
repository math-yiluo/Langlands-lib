# Pulling rational parameter density back to conjugators

Worker 1574. This is an internal interface and conditional deduction for
`RationalMaximalTorusConjugateDensityStatement`. The unrestricted target is
not proved in this module.

`TorusParameterConjugationCompatible j₀ q` describes one required property of
an actual map `q : G → Q` over the ground field. For each ground-field section
`x` of `Q` it provides an actual closed ground-field torus `j : T → G`.
Every algebraic-closure section of `G` lying over the scalar extension of `x`
must conjugate `j₀` onto the scalar extension of `j`. The equality is between
subgroup functors and therefore holds on every scheme test.

This predicate records only conjugation compatibility. It does not define a
quotient, assert representability, construct a universal family, require
maximality, or assert density. The intended example is the quotient map to the
variety of maximal tori, with its universal torus.

The proof has two steps. First,
`dense_rationalPoints_over_dense_parameters` proves a geometric lifting lemma.
Given a nonempty open in the source of an open locally finite type map over an
algebraically closed field, its open image meets a dense collection of rational
parameters. Restricting the map to the source open and applying the published
`exists_rationalPoint_lift_of_mem_range` gives a rational lift inside that open.
Thus rational lifts of the chosen parameters are dense.

Second, `dense_torusConjugators_of_parameters` applies that lemma after scalar
extension, taking the chosen parameters to be the actual scalar extensions of
ground-field sections of `Q`. Conjugation compatibility puts every resulting
lift in the exact good-conjugator set of the Library target. Density passes to
that larger set.

Imported Library inputs are the unchanged target module,
`Langlands.GroupScheme.SchemeActionRationalOrbit` for the rational lifting
lemma, and the paired actual scalar-extension interface
`Langlands.AlgebraicGeometry.PointTopology.GeometricRationalPoints`.
The construction and deduction are internal. Their intended geometric use is
explained by Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), proof of Proposition A.2.11, printed pp.477–478 (one-based PDF
pp.503–504): the actual variety of maximal tori and its universal torus supply
the parameter map and compatibility; its unirationality supplies rational
density over infinite fields. Those existence and density results remain
separate prerequisites here.
