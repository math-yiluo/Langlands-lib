# Cycle representatives for connecting maps

Authors: Worker 45 and Worker 210. Worker 45 wrote the Lean proof; Worker 210
audited it and prepared the accompanying documentation.

This file uses the actual homology objects of cochain complexes of modules.
`cycleClass` sends a cycle representative to its homology class. Its
surjectivity and behavior under negation are proved from the kernel and
homology projection. `delta_cycleClass` specializes Mathlib's proved
representative formula for the connecting map of a short exact sequence
of complexes.

These lemmas support the diagram chase needed for the signs in Serre,
*Local Fields* (1979), Chapter VIII, section 3, Proposition 5, printed
pp. 131–132 (PDF pp. 137–138). They do not themselves assert the cup-product
boundary laws. Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
