# Scalar ideles in actual adelic block parabolics

Author: Worker 2. Provenance: internal construction from the published actual
adelic scalar matrix map and actual block parabolic geometry. This unit makes
no new identification with an original source.

The number field `F : Type uF` has arbitrary universe. Every natural rank `n`
and positive ordered block shape `B` is allowed, including the empty shape in
rank zero. The groups carry the actual matrix-unit and subgroup topologies.

`scalarLevi` sends an actual idele to the tuple of scalar matrices in its
diagonal blocks. It is a continuous homomorphism by the existing continuous
scalar maps and the product topology. `scalar_mem_parabolic` proves that an
ambient scalar matrix belongs to the actual parabolic: two coordinates in
strictly ordered distinct blocks are distinct, so the scalar matrix entry is
zero. `scalarParabolic` is the resulting continuous subgroup-valued map.
Its underlying ambient matrix is precisely the existing adelic scalar matrix.

`leviProjection_scalar` identifies its actual Levi projection with `scalarLevi`.
The proof compares matrix entries and uses injectivity of the coordinate
embedding of each block. `scalarLevi_commute` and `scalarParabolic_commute`
prove centrality in the two actual groups using the existing ambient
scalar-matrix commutation law.

No identification with the entire center or injectivity in rank zero is
asserted. Haar scaling, nonzero induced sections and automorphic existence
remain separate obligations.
