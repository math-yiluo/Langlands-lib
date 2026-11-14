# Descent of a supplied numbered vector eigenbasis

This derived internal module separates scalar descent from representation
existence. The proposition `SplitPinning.NumberedRootFamily` records the three
numbered type-D root equations: differences at successive vertices, the sum at
the last vertex, and every signed sum on distinct coordinates being a root.
The proposition `OrthogonalMatrix.IsCharacterEigenbasis` records the actual
inverse-right row eigenvector identity for a supplied split orthogonal torus
map and basis, over every commutative coefficient algebra.

For an algebraic field extension, `numberedRootFamily_descend` first reindexes
the scalar-extended simple vertices by `baseChangeSimpleEquiv`. It then uses
`SplitRootDatum.numbered_roots_descend`, which applies the inverse of the actual
split-torus character-lattice equivalence. The result is the same three root
equations on the original supplied pinning.

The conditional theorem `numberedVectorBasis_baseChange_of_statement` applies
`NumberedCoverVectorStatement` to a supplied simply connected central cover
over the extension field. It preserves the supplied numbering and Cartan
equality using `baseChangeNumbering_cartan`, retains the all-relative-scheme
kernel-alignment premise, descends the roots, and rewrites the matrix
representation composite as the actual torus map. It returns the characters
over the extension, their descended root equations over the original field,
and the all-coefficient character eigenbasis over the extension.

The numbered-cover statement remains a premise. This module does not prove its
existence claim, construct a Morita comparison, or prove the host vector-weight
theorem. Its provenance is entirely the existing pinning transport, character
descent and matrix-representation definitions, together with that explicit
representation premise. All fields, including characteristic two, and the
universe parameter remain arbitrary.
