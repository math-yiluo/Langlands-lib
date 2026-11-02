# Coordinate-algebra axioms for affine point topologies

Author: Worker 105.

This is a derived intermediate formulation of the uniqueness argument in
Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Proposition 2.1 and its proof, printed pages 2–3.
Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The topology assignment ranges over all actual finite-type coordinate algebras
in `CommAlgCat R`, on the existing actual algebra-map point sets.
`AffineTopologyFunctorial` asks for continuity of every restriction map.
`AffineTopologyQuotientEmbeddings` asks for embeddings under every surjective
coordinate-algebra map; it does not ask for closed images.
`AffineTopologyLine` normalizes the one-variable polynomial algebra by
evaluation of its variable in the given topology of the value ring.

The imported `affinePushoutPointComparison` is the actual map that restricts a point along
the two pushout cocone maps. The cocone's commutativity proves equality of
the restrictions to the common algebra. `AffineTopologyPushouts` requires
this map, for every colimit pushout cocone of finite-type algebras, to be a
homeomorphism to the compatible-pair subspace of the product of factor point
spaces. Thus this interface retains general fibre-product compatibility,
rather than only an assertion about chosen polynomial coordinates.

`AffineTopologyAxioms` conjoins functoriality, pushout compatibility,
quotient embeddings and the line normalization. No additional finite
coproduct axiom is imposed: the uniqueness proof derives the needed
finite-affine-space comparison by empty/option induction from binary
pushouts and the line normalization. The bridge between arbitrary
finite-type affine scheme objects and coordinate-algebra assignments
remains to be proved.
Accordingly this intermediate interface is not yet a statement of the full
scheme formulation of Proposition 2.1.

`AffineTopologyExistenceProperty` says that the evaluation assignment
satisfies all four axioms.
`AffineTopologyUniquenessProperty` says that every assignment satisfying
these requirements equals the existing evaluation assignment as a function
on all finite-type algebras. The value ring has continuous ring operations;
neither the base ring nor coordinate algebras are given topologies.
No Hausdorffness, finite presentation, or nonzero dimension is required.
The base and value ring may have independent universes.
`AffineTopologyCharacterizationProperty` combines existence and uniqueness:
an assignment satisfies the four axioms if and only if it is the evaluation
assignment. These are proposition definitions, not proofs. Their proofs,
the actual scheme bridges, and the source's remaining properties are
independent obligations. The relative base/value-ring formulation is derived
from the source's coordinate proof: every base coefficient is evaluated as a
constant in the value ring, and no topological condition on the base is used.
