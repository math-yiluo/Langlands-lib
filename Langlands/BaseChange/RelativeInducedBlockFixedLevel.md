# Uniform fixed-vector detection on refining blocks

Let `E` be a finite extension of `ℚ_p` with supplied `E.TopologicalData`.
Fix a compact open subgroup of a standard Levi product of general linear
groups over `E` and a block refinement.
`relativeInducedBlockFixedLevel` chooses a compact open subgroup of
each refining block. The inducing factors and the subquotient are smooth
complex representations. If a subquotient of an external tensor of
normalized inductions has a nonzero fixed vector at the original level,
each inducing factor has a nonzero fixed vector at its chosen subgroup.
The universes of the field, the inducing representation carriers and the
subquotient carrier are independent.

Compact-open averaging lifts a fixed vector through the surjection
in the subquotient presentation. Restrict the resulting ambient fixed
vector to the product of the coordinate subgroups lying in the original
level. The tensor product description of fixed vectors detects a nonzero
fixed vector in each normalized induced block. In each block,
`inducedBlockFixedLevel` chooses the levels of the inducing factors from
the finite double-coset cover. This is the fixed-level detection step
used in the argument of Rogawski (1988), §10, Proposition 10.1.
