# Equal closed supports and geometric properties

This derived comparison supports the closure-family step in Stacks Project
Lemma 37.28.4 (055G), used for the geometric connectedness input to Conrad's
Theorem 3.4(2). It uses actual closed immersions, actual scheme pullbacks, and
Mathlib's definitions of geometric connectedness and irreducibility. The schemes
have arbitrary common universe `u`.

For two closed immersions `i : Z ⟶ X` and `j : W ⟶ X` with equal point-set
ranges, `closedImmersionHomeomorphOfRangeEq` is the homeomorphism obtained from
their topological embeddings into their respective ranges, the equality of
these subspaces, and the inverse of the second embedding. It commutes with the
two underlying maps into `X`.

The actual pullback projections along every `p : T ⟶ X` have equal ranges:
Mathlib's pullback range formula identifies them with the inverse images of
the original equal ranges. Their sources are therefore homeomorphic. For any
`f : X ⟶ S` and `e : T ⟶ S`, the pullback-pasting isomorphisms identify these
spaces with the actual pullbacks of `i ≫ f` and `j ≫ f`.

Applying this homeomorphism to every field-spectrum map into `S` proves that
`i ≫ f` is geometrically connected if and only if `j ≫ f` is, and likewise for
geometric irreducibility. These comparisons impose no finite type, flatness,
surjectivity, Noetherianity, affineness or separation hypothesis.

For a closed subset `C` of an actual fibre, the base change of its constructed
closure immersion to that fibre has range exactly `C`. The closed subscheme
defined by the vanishing ideal of `C` has that same range. The construction
`fiberClosedSubsetClosureHomeomorph` compares their underlying spaces.

The pullback-pasting isomorphism also identifies the actual residue-field fibre
of the composite closure immersion and `f` with this pullback.
`fiberClosedSubsetClosureFiberHomeomorph` gives a homeomorphism directly to
`C` with its original subspace topology. Thus connectedness and irreducibility
of the actual fibre are respectively connectedness and irreducibility of `C`.
In particular, the original fibre of the closure of an actual maximal
irreducible component is irreducible. These statements do not require that the
chosen point be generic.

The final two equivalences compare geometric connectedness and geometric
irreducibility of the actual closure fibre over its residue field with those
of the original vanishing-ideal closed subscheme over the same field. The proof
uses the equal-range comparison in the original fibre, then the compatibility
of the pullback-pasting isomorphism with the residue-field projection.
Both geometric properties include nonemptiness, in accordance with Mathlib's
`ConnectedSpace` and `IrreducibleSpace` conventions.

This is a support comparison, not a scheme isomorphism for different possible
nilpotent structures. Geometric irreducibility spreading, finite generic
splitting, and the full generic-constancy theorem remain separate obligations.
