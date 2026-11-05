# Uniform matrix-entry bounds and canonical rational-point compactness

This internal auxiliary statement connects a bound in an actual closed
matrix representation with the canonical topology on all rational points.

`MatrixRepresentation.HasUniformlyBoundedEntries` means that one nonzero
element of the given valued field bounds every entry of every represented
rational point in the multiplicative valuation comparison.

`MatrixEntryBoundedCompactnessStatement` quantifies over every universe `u`,
nonarchimedean local field `F : Type u`, affine actual group scheme over `F`,
natural number `N`, and actual representation into `GL (Fin N)`. If the
representation is a closed subgroup morphism and has uniformly bounded
entries, the whole space of rational points is compact in exactly
`rationalPointTopology F G.X`. It is also algebraically bounded: every global
regular function has its own nonzero uniform valuative bound.

There is no reductivity, connectedness, characteristic, positive-dimension,
or finite-type hypothesis. The empty matrix index is included. The bound is
on the whole point group; applying it to inverse points bounds the inverse
matrix entries as well.

The internal derivation uses the published canonical rational/affine point
comparison and general linear point homeomorphism. A closed representation
therefore gives a closed embedding into the matrix unit group. The standard
closed embedding of units into a matrix and its inverse places its image in
a product of finitely many compact scalar balls. Compactness then bounds
each continuous regular-function evaluation.

This statement supplies only the topological transport after entry bounds
have been proved. It asserts no spectral criterion, group-theoretic spanning
result, or implication from anisotropy, and does not prove the host compactness
equivalence.
