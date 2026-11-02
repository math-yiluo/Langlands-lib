# Actual base change of the supplied-family full-level parameter

Let `A` be a supplied abelian scheme over `S`, let `g,n` be natural
numbers, and let `b : S' ⟶ S` be any scheme morphism. This internal
construction defines an actual isomorphism in `Over S'` between the
full-level parameter of `A` pulled back to `S'` and the scheme-theoretic
pullback of the original full-level parameter. The full-level parameters
require precisely `0 < n` and invertibility of `n` on `S`; the latter
condition is pulled back along `b`. No local noetherian or dimension
hypothesis is needed.

First, `torsionTupleBaseChangeHomEquiv` compares morphisms into the actual
ordered-tuple parameters on every test object `T : Over S'`. It uses the
original torsion base-change linear equivalence on each of the `2g`
coordinates. Its coordinate formula and naturality hold for every
actual morphism of test schemes. These tuple comparisons do not require
positivity or invertibility of `n`.

`sectionTupleBaseChangeEquiv_comp` checks that the decoded ordered
sections agree through `baseChangeCompIso b T.hom A`, the existing
isomorphism between the direct and successive pullbacks of the supplied
abelian scheme. The proof checks equality on underlying section maps,
using the formula for the comparison followed by the first pullback
projection. Transport of the prescribed geometric-fibre bases along
this actual isomorphism proves equivalence of fullness. For the reverse
implication, the inverse and forward tuple transports cancel.

`fullLevelParameterBaseChangeHomEquiv` restricts the tuple comparison
to full tuples and uses the existing full-level parameter
classification. Its inclusion formula identifies its underlying tuple
map exactly, and its naturality follows from the tuple naturality.
`fullLevelParameterBaseChangeHomEquiv_sections` states equality of the
classified ordered sections through the inverse of
`baseChangeCompIso b T.hom A`.

Finally, `fullLevelParameterBaseChangeIso` composes these natural Hom
equivalences with the adjunction between postcomposition and pullback
in the over-categories. The Yoneda construction produces the actual
isomorphism of parameter schemes. The theorem
`fullLevelParameterBaseChangeIso_hom_comp` verifies on every test object
that composition with its forward map is exactly that Hom equivalence
under the pullback adjunction. Together with the preceding section
formula, this specifies its effect on every prescribed coordinate.

The provenance is internal: the construction uses the existing tuple
classifier, torsion base change, abelian-scheme pullback coherence,
preservation of fullness by isomorphisms, and Mathlib's over-category
adjunction and Yoneda construction. It concerns full levels in one
supplied family. It asserts neither numerical torsion rank nor
nonemptiness of the parameter and does not prove automorphism rigidity
or existence of ambient ordinary moduli.
