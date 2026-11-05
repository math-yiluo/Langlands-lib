# Embedding coordinates for Weil-restriction norms

Author: Worker 1587.

This internal algebra interface is derived from the published finite separable
tensor decomposition and Mathlib's Galois norm formula. It describes the tensor
algebra of a finite product of intermediate fields using their embeddings into
a fixed finite Galois extension. Coefficient conjugation acts semilinearly on
these coordinates.

The product supported on the inclusion embedding reduces to the subgroup of
automorphisms fixing the intermediate field. The fixing-subgroup equivalence
with relative automorphisms then identifies this product with the relative
field norm. No boundedness or local norm-surjectivity assertion is made here.
