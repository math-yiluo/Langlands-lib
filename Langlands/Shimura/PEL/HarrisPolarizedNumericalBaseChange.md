# Numerical pointed Harris polarized class pullback

Author: Worker 57.

This internal construction restricts the actual pointed pullback of Harris
polarized determinant classes to the numerical representative image in
`HarrisNumericalWeilTower`. Both the reflex-field structure map `s` and the
CM-field structure map `p` are composed with the actual base morphism `b`.
They remain independent maps; no comparison between them is asserted here.

`levelDataBaseChange_numericalObjectCondition` applies
`HarrisTaylor.numericalCondition_baseChange_of_naturality` to the actual
abelian scheme and rational action of the source representative. Its target
is exactly the abelian scheme and rational action inside `levelDataBaseChange`.
Thus both the actual prescribed geometric relative dimension and the all-chart
central Lie trace formula hold on that constructed representative. The named
`LieBaseChangeNaturalityStatement S` remains an explicit hypothesis.

`harrisClassBaseChange_condition` extracts the existing `ClassCondition`
witness: a single representative with its determinant proof, equality to the
given determinant class, and numerical proof. It pulls back that representative,
uses the existing exact determinant-preservation theorem and the numerical
theorem above, and computes its class using the existing determinant class
pullback. The same pulled-back representative carries both conditions.
No dimension invariance under arbitrary rational isomorphism is used.

`classBaseChange` is the resulting restriction to the existing numerical
`IsoClass` subtype. Its value and representative formulas identify the underlying
determinant class map and the exact constructed representative. In particular,
the construction takes no independently supplied target polarized object.
`classTowerBaseChange` inherits naturality for every original Harris transporter
from the determinant tower transformation by subtype extensionality. This
includes subgroup inclusions and both existing Hecke legs.
`classTowerBaseChange_inclusion` proves the natural square with the numerical
tower's inclusion into the determinant tower.

All named tensor, Picard, dual-naturality and polarization-stability propositions,
the family of dual data constrained to the actual abelian-scheme pullback, the
point and finite-fibre hypotheses, torsion-order and root-of-unity assumptions,
adelic comparison, ordered-pair additivity, and quasi-separated bases are retained
from the imported actual polarized pullback. The field `F` and the auxiliary
field `L` have the CM structures required by the existing numerical condition.
The morphism `b` is arbitrary under these explicit hypotheses; no flatness
assumption is introduced.

The provenance is internal: specialize the existing actual dimension and central
trace pullback theorem, retain the actual satisfying representative in the image
predicate, and restrict the existing quotient and tower maps. Imported definitions
retain their source conventions and citations. This module asserts no normalized
CM comparison, choice independence, successive-base-change coherence, point
independence, unpointed PEL presheaf, representability, scheme levels, canonical
model or coefficient descent.
