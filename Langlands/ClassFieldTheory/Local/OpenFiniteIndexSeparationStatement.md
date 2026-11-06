# Separation by open finite-index subgroups

`Langlands.LocalClassField.OpenFiniteIndexSubgroupsSeparatePoints` states that,
for every prime, actual p-adic field in an arbitrary carrier universe, and
supplied `PadicField.TopologicalData`, each nonidentity element of the field's
multiplicative group is excluded by an open subgroup of finite index. Openness
uses that supplied field topology and Mathlib's resulting topology on units.
The subgroup and its index are the actual Mathlib objects.

This is a derived internal prerequisite for
`Langlands.LocalClassField.NormSubgroupsSeparatePoints`. Its formulation comes
from the published actual local-field topology and unit constructions. It
isolates the topological separation step from the arithmetic assertion
`NormSubgroupExistence`: realization of the excluding subgroup as a norm group
would imply the desired norm separation. The statement introduces no
reciprocity map and asserts no norm-existence theorem. It is a proposition
definition; this module supplies no proof.
