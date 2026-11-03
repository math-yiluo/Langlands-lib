# Finiteness of the full normalizer image of a split torus

Author: Worker 1283.

`Langlands.GroupScheme.SplitTorusWeylImageFiniteStatement` states that a
closed split torus in an affine algebraic group over a field has finite
normalizer image on its entire integral character lattice. The Lean file
defines this proposition and supplies no proof.

The quantifiers range over every field `k : Type u`, an affine group scheme
`G` locally of finite type over `Spec k`, a commutative group scheme `T`
with `IsSplitTorus T.toGrp`, and a closed group embedding
`i : T.toGrp ⟶ G`. Affineness over a field implies quasi-compactness, so
these finiteness assumptions make `G` an algebraic group in the source's
sense. Neither `G` nor its kernel, centre or normalizer is assumed smooth,
connected or reductive. The torus need not be maximal. The closed
embedding supplies the monomorphism instance needed by `weylImage`.
The index set of the split torus is finite by `IsSplitTorus`, and rank zero
is included.

The conclusion concerns the published subgroup
`weylImage i = (weylAction i).range`, with the action of actual normalizing
`k`-points on `characterLattice T`. It is a statement about the full
lattice, including directions outside the span of the adjoint roots. No
faithfulness on the root span, root-system structure, spanning by roots
and restricted group characters, or root-datum existence is assumed.

The statement is derived from J. S. Milne, *Algebraic Groups* (2017), source
`milne-2017-algebraic-groups`, Theorem 12.36 and Corollary 12.40, printed
pp.243–244 (PDF pp.259–260). Corollary 12.40 says that for a subgroup of
multiplicative type the normalizer and centralizer have the same identity
component, or equivalently that the centralizer is open in the normalizer.
The finite-type normalizer has finitely many connected components. Its
quotient by the centralizer is therefore finite, and the action on the
character lattice factors through that quotient. The split-torus
character functor is faithful, as expressed by the existing Library's
normalizer-action and centralizer lemmas. Finiteness of the resulting
image on actual `k`-points is the asserted consequence. The statement
does not identify a scheme quotient with a quotient of rational points.

The retained official errata, source
`milne-2017-algebraic-groups-errata-2026-11-02`, correct Corollary 12.41 on
p.244, requiring a central subgroup in that different extension statement.
They do not correct Theorem 12.36 or Corollary 12.40. No use of 12.41 is
made here.

This general algebraic-group fact is a prerequisite for identifying the
coroots of supplied actual root data: two normalizer reflections along
the same root have a finite-order product on the character lattice.
It is separate from the proof of the central-isogeny root comparison and
from its isomorphism criterion.
