# The full-lattice torus in the generic Chevalley closure

This internal construction factors the actual diagonalizable group of the
full character lattice through the generic Chevalley closure over a Dedekind
domain. It uses the specified fraction field and the chosen generic Chevalley
group; no field fibres are chosen afterward.

The matrix torus representation respects arbitrary base change. On each test
scheme, both sides give the same diagonal matrix for the same character with
values in global units. The proof uses the published diagonalizable and
general linear base-change isomorphisms.

The diagonalizable group is flat over its base because its coordinate group
algebra is a free module. Its generic-fibre projection is therefore
schematically dominant. The generic torus maps into the chosen Chevalley
group by its existing torus homomorphism. Its composite into the matrix group
is the generic fibre of the integral matrix torus homomorphism. Factorization
through the closed generic closure descends along that schematically
dominant projection.

The chosen factor `torusOver` preserves the group laws because its composite
with the closed model inclusion does and that inclusion is a monomorphism.
It therefore defines the group-scheme homomorphism `torus`. Its matrix
composite is the original integral diagonal representation, which is a
closed immersion by full-lattice generation; cancellation of a closed
immersion then shows that `torus` is itself a closed subgroup. The matrix
composite also uniquely characterizes the factor. On the specified generic
fibre, it is the original torus map `C.t` under the published diagonalizable
base-change isomorphism and the model's generic isomorphism.

The provenance is internal: these are consequences of the published matrix
maps, diagonalizable base-change comparison, generic closure, and schematic
dominance factorization. Smoothness or reductivity of the integral closure
and its full field-fibre root-datum comparison remain separate obligations.
